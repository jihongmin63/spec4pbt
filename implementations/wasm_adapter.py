"""External adapter binding Wasm `Module_ok` / `Module_init_ok` to a real engine.

Usage: `python implementations/wasm_adapter.py {wasmtime|node}` with one JSON
request on stdin (see README "Binding an implementation"). The canonical
relation input is `[module]`. The adapter encodes it with `wasm_encoder`,
rejects modules beyond the engine's documented implementation limits, runs the
engine, and classifies the outcome:

  Module_ok      success: the engine validates the binary
                 relation_failure: the engine reports a validation error
  Module_init_ok success: the engine validates it, instantiates it with no
                 imports, and the start function (if any) returns normally
                 relation_failure: validation error, missing import, trap, or
                 uncaught Wasm exception
  abort (both)   unencodable AST, implementation limit, resource exhaustion
                 (call stack, allocation), timeout, or an unclassified error

Both catalog entries observe nothing, so every success observation is `{}`.
Diagnostics go to stderr; stdout carries exactly one JSON response.
"""

import json
import os
import re
import subprocess
import sys
import threading
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from wasm_encoder import Unencodable, encode_module_details  # noqa: E402

RELATIONS = ('Module_ok', 'Module_init_ok')
IDENTITIES = ('plan_id', 'case_id', 'occurrence_id', 'relation_id')
NODE = HERE / 'local/node/node-v26.13.0-linux-x64/bin/node'
NODE_DRIVER = HERE / 'wasm_node_driver.mjs'


def timeout_seconds():
    try:
        return max(1.0, float(os.environ.get('SPEC4PBT_WASM_TIMEOUT', '20')))
    except ValueError:
        return 20.0


class Outcome(Exception):
    def __init__(self, status, message=None):
        super().__init__(message or status)
        self.status, self.message = status, message


def unmatch(reason):
    return Outcome('relation_failure', reason)


def abort(reason):
    return Outcome('abort', reason)


# ---------------------------------------------------------------------------
# Implementation limits (trusted boundary: beyond these an engine may reject a
# valid module or fail for resource reasons, so the case is an error, not a
# verdict). Sources: WebAssembly JS API "Implementation-defined Limits",
# wasmparser limits.rs (Wasmtime), and measurements of V8 14.6 / Wasmtime 50.

COMMON_LIMITS = {
    'types': 1_000_000, 'rec groups': 1_000_000, 'functions': 1_000_000,
    'imports': 1_000_000, 'exports': 1_000_000, 'globals': 1_000_000,
    'tags': 1_000_000, 'data segments': 100_000, 'element segments': 100_000,
    'tables': 100_000, 'function params': 1000, 'function results': 1000,
    'function locals': 50_000, 'function body bytes': 7_654_321,
    'module bytes': 1 << 30, 'struct fields': 10_000, 'subtyping depth': 63,
    'name bytes': 100_000, 'catch clauses': 10_000,
    'element segment entries': 10_000_000,
}
ENGINE_LIMITS = {
    'wasmtime': {'memories': 100},
    'node': {'memory64 pages': 262_144, 'table initial size': 10_000_000,
             'array.new_fixed operands': 10_000},
}


def _check(engine, label, value):
    limit = {**COMMON_LIMITS, **ENGINE_LIMITS[engine]}.get(label)
    if limit is not None and value > limit:
        raise abort(f'implementation limit ({engine}): {label} {value} exceeds {limit}')


def _ctor(value):
    if isinstance(value, str):
        return value, None
    if isinstance(value, dict) and len(value) == 1:
        return next(iter(value.items()))
    return None, None


def _walk_instrs(instrs, visit):
    for instr in instrs if isinstance(instrs, list) else []:
        name, payload = _ctor(instr)
        visit(name, payload)
        if name in ('BLOCK', 'LOOP') and isinstance(payload, list) and len(payload) == 2:
            _walk_instrs(payload[1], visit)
        elif name == 'IF % % ELSE %' and isinstance(payload, list) and len(payload) == 3:
            _walk_instrs(payload[1], visit)
            _walk_instrs(payload[2], visit)
        elif name == 'TRY_TABLE' and isinstance(payload, list) and len(payload) == 3:
            _walk_instrs(payload[2], visit)


def check_limits(module, engine, binary, details):
    """Raise abort when an encodable module exceeds the engine's limits."""
    _check(engine, 'module bytes', len(binary))
    types = module['TYPES']
    _check(engine, 'rec groups', len(types))
    subtypes = []  # (absolute index, supertype indices, strtype)
    for group in types:
        _, subs = _ctor(group)
        base = len(subtypes)
        for sub in subs or []:
            _, (final, supers, strtype) = _ctor(sub)
            indices = []
            for heap in supers:
                _, var = _ctor(heap)
                kind, index = _ctor(var)
                indices.append(index if kind == 'StatX' else base + index)
            subtypes.append((len(subtypes), indices, strtype))
    _check(engine, 'types', len(subtypes))
    depth = {}
    for index, supers, strtype in subtypes:
        known = [depth[s] for s in supers if s in depth]
        depth[index] = 1 + max(known) if known else 0
        _check(engine, 'subtyping depth', depth[index])
        kind, body = _ctor(strtype)
        if kind == 'DefFuncT':
            _, (params, results) = _ctor(body)
            _check(engine, 'function params', len(params))
            _check(engine, 'function results', len(results))
        elif kind == 'DefStructT':
            _, fields = _ctor(body)
            _check(engine, 'struct fields', len(fields))
    func_params = {}
    for index, _, strtype in subtypes:
        kind, body = _ctor(strtype)
        if kind == 'DefFuncT':
            func_params[index] = len(_ctor(body)[1][0])
    imports = module['IMPORTS']
    _check(engine, 'imports', len(imports))
    imported = {'TableImport': 0, 'MemImport': 0}
    for imp in imports:
        kind, _ = _ctor(imp['IDESC'])
        if kind in imported:
            imported[kind] += 1
        for key in ('MODULENAME', 'ITEMNAME'):
            _check(engine, 'name bytes', len(''.join(map(chr, imp[key])).encode('utf-8', 'surrogatepass')))
    for label, key in (('functions', 'FUNCS'), ('exports', 'EXPORTS'), ('globals', 'GLOBALS'),
                       ('tags', 'TAGS'), ('data segments', 'DATAS'), ('element segments', 'ELEMS')):
        _check(engine, label, len(module[key]))
    for export in module['EXPORTS']:
        _check(engine, 'name bytes', len(''.join(map(chr, export['NAME'])).encode('utf-8', 'surrogatepass')))
    _check(engine, 'tables', len(module['TABLES']) + imported['TableImport'])
    _check(engine, 'memories', len(module['MEMS']) + imported['MemImport'])
    memtypes = [m['MTYPE'] for m in module['MEMS']]
    tabletypes = [t['TTYPE'] for t in module['TABLES']]
    for imp in imports:
        kind, desc = _ctor(imp['IDESC'])
        if kind == 'MemImport':
            memtypes.append(desc)
        elif kind == 'TableImport':
            tabletypes.append(desc)
    for memtype in memtypes:
        _, (addrtype, lim) = _ctor(memtype)
        if addrtype == 'I64AT':
            _check(engine, 'memory64 pages', lim['MIN'])
            if lim['MAX'] is not None:
                _check(engine, 'memory64 pages', lim['MAX'])
    for tabletype in tabletypes:
        _, (addrtype, lim, _ref) = _ctor(tabletype)
        _check(engine, 'table initial size', lim['MIN'])
    for elem in module['ELEMS']:
        _check(engine, 'element segment entries', len(elem['EINIT']))
    for size in details['code_sizes']:
        _check(engine, 'function body bytes', size)

    def visit(name, payload):
        if name == 'ARRAY.NEW_FIXED' and isinstance(payload, list):
            _check(engine, 'array.new_fixed operands', payload[1])
        elif name == 'TRY_TABLE' and isinstance(payload, list):
            _check(engine, 'catch clauses', len(payload[1]))

    for func in module['FUNCS']:
        _check(engine, 'function locals', len(func['LOCALS']) + func_params.get(func['FTYPE'], 0))
        _walk_instrs(func['BODY'], visit)
    for expr in ([g['GINIT'] for g in module['GLOBALS']] + [t['TINIT'] for t in module['TABLES']]
                 + [x for e in module['ELEMS'] for x in e['EINIT']]):
        _walk_instrs(expr, visit)


# ---------------------------------------------------------------------------
# Engines. Decoding markers are a safety net: the encoder only emits
# well-formed binaries, so a decoding error indicates an encoder defect and
# must not count as the engine's validation verdict.

WASMTIME_DECODING = ('unexpected end', 'malformed', 'invalid leb128', 'integer representation too long',
                     'integer too large', 'section size mismatch', 'illegal opcode',
                     'unexpected content after last section', 'invalid leading byte',
                     'zero byte expected', 'data count section required', 'inconsistent lengths',
                     'section out of order')
WASMTIME_LIMITS = ('count exceeds limit', 'too many locals', 'hierarchy too deep', 'size is out of bounds')
WASMTIME_RESOURCE = ('mmap failed', 'out of memory', 'cannot allocate', 'gc heap', 'insufficient resources')
V8_DECODING = ('fell off end', 'invalid opcode', 'section was shorter', 'section was longer', 'extra bytes',
               'invalid section code', 'expected magic', 'expected version', 'unexpected section',
               'invalid leb', 'out of order')
V8_LIMITS = ('implementation limit', 'internal limit', 'too large, maximum is', 'local count too large',
             'subtyping depth is greater than allowed')
V8_RESOURCE = ('requested new array is too large', 'out of memory', 'maximum call stack size exceeded')


def _first_line(text):
    return (text or '').strip().splitlines()[0] if (text or '').strip() else ''


def _invalid(message, decoding, limits, engine):
    lowered = message.lower()
    if any(marker in lowered for marker in decoding):
        return abort(f'{engine} failed to decode the encoded binary (possible encoder defect): {message}')
    if any(marker in lowered for marker in limits):
        return abort(f'implementation limit ({engine}): {message}')
    return unmatch(f'{engine} validation error: {message}')


def run_wasmtime(relation, binary):
    import wasmtime

    config = wasmtime.Config()
    config.epoch_interruption = True
    engine = wasmtime.Engine(config)
    try:
        wasmtime.Module.validate(engine, binary)
    except wasmtime.WasmtimeError as error:
        raise _invalid(_first_line(str(error)), WASMTIME_DECODING, WASMTIME_LIMITS, 'wasmtime')
    if relation == 'Module_ok':
        return
    try:
        module = wasmtime.Module(engine, binary)
    except wasmtime.WasmtimeError as error:
        raise abort(f'wasmtime failed to compile a validated module: {_first_line(str(error))}')
    store = wasmtime.Store(engine)
    store.set_epoch_deadline(1)
    timer = threading.Timer(timeout_seconds(), engine.increment_epoch)
    timer.daemon = True
    timer.start()
    try:
        wasmtime.Instance(store, module, [])
    except wasmtime.Trap as trap:
        code = trap.trap_code
        detail = ' '.join(str(trap).split())
        if code in (wasmtime.TrapCode.INTERRUPT, wasmtime.TrapCode.OUT_OF_FUEL):
            raise abort(f'wasmtime timeout after {timeout_seconds()}s')
        if code in (wasmtime.TrapCode.STACK_OVERFLOW, wasmtime.TrapCode.ALLOCATION_TOO_LARGE):
            raise abort(f'wasmtime resource exhaustion ({code}): {detail}')
        if code == wasmtime.TrapCode.UNCAUGHT_EXCEPTION:
            raise unmatch(f'wasmtime uncaught exception: {detail}')
        if code is None:
            raise abort(f'wasmtime trap without a trap code: {detail}')
        raise unmatch(f'wasmtime trap ({code}): {detail}')
    except wasmtime.WasmtimeError as error:
        text = str(error)
        lowered = text.lower()
        if 'thrown wasm exception' in lowered:
            raise unmatch('wasmtime uncaught exception')
        if re.search(r'expected \d+ imports?, found \d+', lowered):
            raise unmatch(f'wasmtime link error: {_first_line(text)}')
        if any(marker in lowered for marker in WASMTIME_RESOURCE):
            raise abort(f'wasmtime resource exhaustion: {" ".join(text.split())}')
        raise abort(f'wasmtime unclassified instantiation error: {" ".join(text.split())}')
    finally:
        timer.cancel()


def run_node(relation, binary):
    mode = 'validate' if relation == 'Module_ok' else 'instantiate'
    try:
        result = subprocess.run([str(NODE), '--no-warnings', str(NODE_DRIVER), mode], input=binary,
                                capture_output=True, timeout=timeout_seconds(), check=False)
    except subprocess.TimeoutExpired:
        raise abort(f'node timeout after {timeout_seconds()}s')
    if result.returncode != 0:
        raise abort(f'node driver exited with {result.returncode}: '
                    + _first_line(result.stderr.decode('utf-8', 'replace')))
    try:
        report = json.loads(result.stdout)
    except ValueError:
        raise abort('node driver produced malformed output')
    if report.get('ok'):
        return
    stage, kind, message = report.get('stage'), report.get('class'), report.get('message') or ''
    if stage == 'compile':
        if kind == 'CompileError':
            raise _invalid(message, V8_DECODING, V8_LIMITS, 'node')
        raise abort(f'node unclassified compile error {kind}: {message}')
    lowered = message.lower()
    if report.get('wasm_exception'):
        raise unmatch('node uncaught WebAssembly.Exception')
    if kind in ('RuntimeError', 'RangeError') and any(marker in lowered for marker in V8_RESOURCE):
        raise abort(f'node resource exhaustion ({kind}): {message}')
    if kind == 'RuntimeError':
        raise unmatch(f'node trap: {message}')
    if kind in ('LinkError', 'TypeError'):
        raise unmatch(f'node link error ({kind}): {message}')
    raise abort(f'node unclassified instantiation error {kind}: {message}')


ENGINES = {'wasmtime': run_wasmtime, 'node': run_node}


# ---------------------------------------------------------------------------

def respond(request, engine):
    if request.get('relation_id') not in RELATIONS:
        raise abort(f'unsupported relation {request.get("relation_id")!r}')
    if request.get('observe') != []:
        raise abort('Module_ok and Module_init_ok expose no observable outputs')
    value = request.get('input')
    if not isinstance(value, list) or len(value) != 1:
        raise abort('expected the relation input [module]')
    module = value[0]
    try:
        binary, details = encode_module_details(module)
    except Unencodable as error:
        raise abort(f'unencodable module: {error}')
    check_limits(module, engine, binary, details)
    ENGINES[engine](request['relation_id'], binary)


def main(argv):
    if len(argv) != 2 or argv[1] not in ENGINES:
        print('usage: wasm_adapter.py {wasmtime|node}', file=sys.stderr)
        return 2
    request = json.load(sys.stdin)
    response = {key: request.get(key) for key in IDENTITIES}
    try:
        respond(request, argv[1])
        response.update(status='success', observation={})
    except Outcome as outcome:
        response['status'] = outcome.status
        if outcome.status == 'abort':
            response['message'] = outcome.message
        print(f'{argv[1]}: {outcome.status}: {outcome.message}', file=sys.stderr)
    print(json.dumps(response))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
