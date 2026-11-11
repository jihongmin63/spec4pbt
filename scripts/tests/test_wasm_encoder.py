"""Wasm binary encoder used by implementations/wasm_adapter.py.

Golden-byte and Unencodable tests always run. The cross-checks compare the
encoder with Wasmtime's independent text assembler (wasmtime.wat2wasm, no
validation): the opcode check assembles the official text mnemonic of every
table entry, and the module check assembles whole modules, handwritten ones
covering every section kind and seeded random ones covering type sections,
limits, names and constants. They are skipped unless
implementations/local/wasmtime-venv is installed.
"""
import json
import random
import subprocess
import sys
import unittest

from scripts.tests import ROOT

sys.path.insert(0, str(ROOT / 'implementations'))
import wasm_encoder as enc  # noqa: E402

WASMTIME_PYTHON = ROOT / 'implementations/local/wasmtime-venv/bin/python'

I32, I64, F32, F64, V128 = ({'NumT': 'I32T'}, {'NumT': 'I64T'}, {'NumT': 'F32T'},
                            {'NumT': 'F64T'}, {'VecT': 'V128T'})


def ref(null, heap):
    return {'% %': ['Null' if null else 'NoNull', heap]}


def functype(params=(), results=()):
    return {'RecT': [{'SubT': ['Final', [], {'DefFuncT': {'FuncT': [list(params), list(results)]}}]}]}


def module(**fields):
    base = {'TYPES': [], 'GLOBALS': [], 'TABLES': [], 'MEMS': [], 'TAGS': [], 'FUNCS': [],
            'START': None, 'ELEMS': [], 'DATAS': [], 'IMPORTS': [], 'EXPORTS': []}
    base.update(fields)
    return base


def memop(type_, pack, align=0, offset=0):
    return {'TYPE': type_, 'ALIGN': align, 'OFFSET': offset, 'PACK': pack}


def instr(value):
    return enc._Encoder().instr(value, 'test')


# Spec AST name -> official text mnemonic. These tables are written
# independently of the encoder's opcode tables and checked against wat2wasm.
BIN_TEXT = {'IAdd': 'add', 'ISub': 'sub', 'IMul': 'mul', 'IDivS': 'div_s', 'IDivU': 'div_u',
            'IRemS': 'rem_s', 'IRemU': 'rem_u', 'IAnd': 'and', 'IOr': 'or', 'IXor': 'xor',
            'IShl': 'shl', 'IShrS': 'shr_s', 'IShrU': 'shr_u', 'IRotl': 'rotl', 'IRotr': 'rotr',
            'FAdd': 'add', 'FSub': 'sub', 'FMul': 'mul', 'FDiv': 'div', 'FMin': 'min', 'FMax': 'max',
            'FCopysign': 'copysign'}
REL_TEXT = {'Eq': 'eq', 'Ne': 'ne', 'LtS': 'lt_s', 'LtU': 'lt_u', 'GtS': 'gt_s', 'GtU': 'gt_u',
            'LeS': 'le_s', 'LeU': 'le_u', 'GeS': 'ge_s', 'GeU': 'ge_u', 'Lt': 'lt', 'Gt': 'gt',
            'Le': 'le', 'Ge': 'ge'}
UN_TEXT = {'Clz': 'clz', 'Ctz': 'ctz', 'Popcnt': 'popcnt', 'Abs': 'abs', 'Neg': 'neg',
           'Ceil': 'ceil', 'Floor': 'floor', 'Trunc': 'trunc', 'Nearest': 'nearest', 'Sqrt': 'sqrt'}
CVT_TEXT = {('I32', 'WrapI64'): 'i32.wrap_i64',
            ('I32', 'TruncSF32'): 'i32.trunc_f32_s', ('I32', 'TruncUF32'): 'i32.trunc_f32_u',
            ('I32', 'TruncSF64'): 'i32.trunc_f64_s', ('I32', 'TruncUF64'): 'i32.trunc_f64_u',
            ('I64', 'ExtendSI32'): 'i64.extend_i32_s', ('I64', 'ExtendUI32'): 'i64.extend_i32_u',
            ('I64', 'TruncSF32'): 'i64.trunc_f32_s', ('I64', 'TruncUF32'): 'i64.trunc_f32_u',
            ('I64', 'TruncSF64'): 'i64.trunc_f64_s', ('I64', 'TruncUF64'): 'i64.trunc_f64_u',
            ('F32', 'ConvertSI32'): 'f32.convert_i32_s', ('F32', 'ConvertUI32'): 'f32.convert_i32_u',
            ('F32', 'ConvertSI64'): 'f32.convert_i64_s', ('F32', 'ConvertUI64'): 'f32.convert_i64_u',
            ('F32', 'DemoteF64'): 'f32.demote_f64',
            ('F64', 'ConvertSI32'): 'f64.convert_i32_s', ('F64', 'ConvertUI32'): 'f64.convert_i32_u',
            ('F64', 'ConvertSI64'): 'f64.convert_i64_s', ('F64', 'ConvertUI64'): 'f64.convert_i64_u',
            ('F64', 'PromoteF32'): 'f64.promote_f32',
            ('I32', 'ReinterpretFloat'): 'i32.reinterpret_f32', ('I64', 'ReinterpretFloat'): 'i64.reinterpret_f64',
            ('F32', 'ReinterpretInt'): 'f32.reinterpret_i32', ('F64', 'ReinterpretInt'): 'f64.reinterpret_i64',
            ('I32', 'TruncSatSF32'): 'i32.trunc_sat_f32_s', ('I32', 'TruncSatUF32'): 'i32.trunc_sat_f32_u',
            ('I32', 'TruncSatSF64'): 'i32.trunc_sat_f64_s', ('I32', 'TruncSatUF64'): 'i32.trunc_sat_f64_u',
            ('I64', 'TruncSatSF32'): 'i64.trunc_sat_f32_s', ('I64', 'TruncSatUF32'): 'i64.trunc_sat_f32_u',
            ('I64', 'TruncSatSF64'): 'i64.trunc_sat_f64_s', ('I64', 'TruncSatUF64'): 'i64.trunc_sat_f64_u'}
LOAD_TEXT = {('I32T', None): 'i32.load', ('I64T', None): 'i64.load', ('F32T', None): 'f32.load',
             ('F64T', None): 'f64.load'}
for _t in ('I32T', 'I64T'):
    for _p, _n in (('I8', '8'), ('I16', '16'), ('I32', '32')):
        for _e, _s in (('SX', 's'), ('ZX', 'u')):
            if not (_t == 'I32T' and _p == 'I32'):
                LOAD_TEXT[(_t, _p, _e)] = f'{_t[:3].lower()}.load{_n}_{_s}'
STORE_TEXT = {('I32T', None): 'i32.store', ('I64T', None): 'i64.store', ('F32T', None): 'f32.store',
              ('F64T', None): 'f64.store', ('I32T', 'I8'): 'i32.store8', ('I32T', 'I16'): 'i32.store16',
              ('I64T', 'I8'): 'i64.store8', ('I64T', 'I16'): 'i64.store16', ('I64T', 'I32'): 'i64.store32'}
VBIN_TEXT = {'Swizzle': 'swizzle', 'Add': 'add', 'AddSatS': 'add_sat_s', 'AddSatU': 'add_sat_u',
             'Sub': 'sub', 'SubSatS': 'sub_sat_s', 'SubSatU': 'sub_sat_u', 'MinS': 'min_s',
             'MinU': 'min_u', 'MaxS': 'max_s', 'MaxU': 'max_u', 'AvgrU': 'avgr_u', 'Mul': 'mul',
             'Q15MulRSatS': 'q15mulr_sat_s', 'RelaxedSwizzle': 'relaxed_swizzle',
             'RelaxedQ15MulRS': 'relaxed_q15mulr_s', 'RelaxedDot': 'relaxed_dot_i8x16_i7x16_s',
             'DotS': 'dot_i16x8_s', 'Div': 'div', 'Min': 'min', 'Max': 'max', 'Pmin': 'pmin',
             'Pmax': 'pmax', 'RelaxedMin': 'relaxed_min', 'RelaxedMax': 'relaxed_max'}
NARROWER = {'I8x16': None, 'I16x8': 'i8x16', 'I32x4': 'i16x8', 'I64x2': 'i32x4'}
WIDER = {'I8x16': 'i16x8', 'I16x8': 'i32x4'}
VCVT_TEXT = {'TruncSatSF32x4': 'trunc_sat_f32x4_s', 'TruncSatUF32x4': 'trunc_sat_f32x4_u',
             'TruncSatSZeroF64x2': 'trunc_sat_f64x2_s_zero', 'TruncSatUZeroF64x2': 'trunc_sat_f64x2_u_zero',
             'RelaxedTruncSF32x4': 'relaxed_trunc_f32x4_s', 'RelaxedTruncUF32x4': 'relaxed_trunc_f32x4_u',
             'RelaxedTruncSZeroF64x2': 'relaxed_trunc_f64x2_s_zero',
             'RelaxedTruncUZeroF64x2': 'relaxed_trunc_f64x2_u_zero',
             'DemoteZeroF64x2': 'demote_f64x2_zero', 'PromoteLowF32x4': 'promote_low_f32x4'}


def vbin_text(shape, op):
    lane = shape.lower()
    if op in ('NarrowS', 'NarrowU'):
        return f'{lane}.narrow_{WIDER[shape]}_{op[-1].lower()}'
    if op.startswith('ExtMul'):
        half = 'low' if 'Low' in op else 'high'
        return f'{lane}.extmul_{half}_{NARROWER[shape]}_{op[-1].lower()}'
    return f'{lane}.{VBIN_TEXT[op]}'


def vcvt_text(shape, op):
    lane = shape.lower()
    if op.startswith('Extend') or op.startswith('ExtAddPairwise'):
        source = {'I16x8': 'i8x16', 'I32x4': 'i16x8', 'I64x2': 'i32x4'}[shape]
        sign = op[-1].lower()
        if op.startswith('ExtAddPairwise'):
            return f'{lane}.extadd_pairwise_{source}_{sign}'
        half = 'low' if 'Low' in op else 'high'
        return f'{lane}.extend_{half}_{source}_{sign}'
    if op.startswith('Convert'):
        low = '_low' if shape == 'F64x2' else ''
        return f'{lane}.convert{low}_i32x4_{op[7].lower()}'
    return f'{lane}.{VCVT_TEXT[op]}'


def opcode_cases():
    """Yield (spec instruction JSON, text instruction) for every table entry."""
    for kind, op in enc.BINOP:
        yield {'BINOP': {kind: op}}, f'{kind.lower()}.{BIN_TEXT[op]}'
    for kind, op in enc.RELOP:
        yield {'COMPARE': {kind: op}}, f'{kind.lower()}.{REL_TEXT[op]}'
    for kind, op in enc.UNOP:
        yield {'UNARY': {kind: op}}, f'{kind.lower()}.{UN_TEXT[op]}'
    for kind, pack in enc.EXTENDS:
        yield {'UNARY': {kind: {'ExtendS': pack}}}, f'{kind.lower()}.extend{pack[1:]}_s'
    for kind, op in enc.TESTOP:
        yield {'TEST': {kind: op}}, f'{kind.lower()}.eqz'
    for key in enc.CVTOP:
        yield {'CONVERT': {key[0]: key[1]}}, CVT_TEXT[key]
    for key in enc.LOAD:
        pack = None if key[1] is None else [key[1], key[2]]
        yield {'LOAD': [0, memop(key[0], pack, 1, 16)]}, f'{LOAD_TEXT[key]} offset=16 align=2'
    for key in enc.STORE:
        yield {'STORE': [2, memop(key[0], key[1], 0, 3)]}, f'{STORE_TEXT[key]} 2 offset=3 align=1'
    vec = lambda op: {'V128': op}
    for shape, op in enc.VTEST:
        yield {'VEC.TEST': vec({shape: op})}, f'{shape.lower()}.all_true'
    for shape, op in enc.VUNOP:
        yield {'VEC.UNARY': vec({shape: op})}, f'{shape.lower()}.{UN_TEXT[op]}'
    for shape, op in enc.VBINOP:
        yield {'VEC.BINARY': vec({shape: op})}, vbin_text(shape, op)
    for shape, op in enc.VTERNOP:
        text = {'RelaxedLaneselect': 'relaxed_laneselect', 'RelaxedDotAdd': 'relaxed_dot_i8x16_i7x16_add_s',
                'RelaxedMadd': 'relaxed_madd', 'RelaxedNmadd': 'relaxed_nmadd'}[op]
        yield {'VEC.TERNARY': vec({shape: op})}, f'{shape.lower()}.{text}'
    for shape, op in enc.VRELOP:
        yield {'VEC.COMPARE': vec({shape: op})}, f'{shape.lower()}.{REL_TEXT[op]}'
    for shape, op in enc.VCVTOP:
        yield {'VEC.CONVERT': vec({shape: op})}, vcvt_text(shape, op)
    for shape, op in enc.VSHIFT:
        yield {'VEC.SHIFT': vec({shape: op})}, f'{shape.lower()}.{ {"Shl": "shl", "ShrS": "shr_s", "ShrU": "shr_u"}[op]}'
    for shape, op in enc.VBITMASK:
        yield {'VEC.BITMASK': vec({shape: op})}, f'{shape.lower()}.bitmask'
    yield {'VEC.TESTBITS': vec('AnyTrue')}, 'v128.any_true'
    yield {'VEC.UNARYBITS': vec('Not')}, 'v128.not'
    for op, text in (('And', 'and'), ('AndNot', 'andnot'), ('Or', 'or'), ('Xor', 'xor')):
        yield {'VEC.BINARYBITS': vec(op)}, f'v128.{text}'
    yield {'VEC.TERNARYBITS': vec('Bitselect')}, 'v128.bitselect'
    for shape in enc.VSPLAT:
        yield {'VEC.SPLAT': vec({shape: 'Splat'})}, f'{shape.lower()}.splat'
    for (shape, ext), _ in enc.VEXTRACT.items():
        suffix = '' if ext == 'VOID' else '_' + ('s' if ext == 'SX' else 'u')
        yield {'VEC.EXTRACT': vec({shape: {'Extract': [1, ext]}})}, f'{shape.lower()}.extract_lane{suffix} 1'
    for shape in enc.VREPLACE:
        yield {'VEC.REPLACE': vec({shape: {'Replace': 1}})}, f'{shape.lower()}.replace_lane 1'
    v = lambda pack: memop('V128T', pack, 0, 8)
    yield {'VEC.LOAD': [0, v(None)]}, 'v128.load offset=8 align=1'
    for (packtype, shape, ext) in enc.VLOAD_LANE:
        text = {'Pack8x8': '8x8', 'Pack16x4': '16x4', 'Pack32x2': '32x2'}[shape]
        yield ({'VEC.LOAD': [0, v([packtype, {'ExtLane': [shape, ext]}])]},
               f'v128.load{text}_{"s" if ext == "SX" else "u"} offset=8 align=1')
    for packtype in enc.VLOAD_SPLAT:
        yield {'VEC.LOAD': [0, v([packtype, 'ExtSplat'])]}, f'v128.load{packtype[1:]}_splat offset=8 align=1'
    for packtype in enc.VLOAD_ZERO:
        yield {'VEC.LOAD': [0, v([packtype, 'ExtZero'])]}, f'v128.load{packtype[1:]}_zero offset=8 align=1'
    yield {'VEC.STORE': [0, memop('V128T', 'VOID', 0, 8)]}, 'v128.store offset=8 align=1'
    for packtype in enc.VLANE_LOAD:
        yield ({'VEC.LOAD_LANE': [0, memop('V128T', packtype, 0, 8), 1]},
               f'v128.load{packtype[1:]}_lane offset=8 align=1 1')
    for packtype in enc.VLANE_STORE:
        yield ({'VEC.STORE_LANE': [0, memop('V128T', packtype, 0, 8), 1]},
               f'v128.store{packtype[1:]}_lane offset=8 align=1 1')


STRUCTURED_CASES = [
    ('UNREACHABLE', 'unreachable'), ('NOP', 'nop'), ('DROP', 'drop'), ({'SELECT': None}, 'select'),
    ({'SELECT': [I64]}, 'select (result i64)'), ('RETURN', 'return'), ('THROW_REF', 'throw_ref'),
    ({'BLOCK': [{'ValBlockType': I32}, ['NOP']]}, 'block (result i32) nop end'),
    ({'BLOCK': [{'VarBlockType': 3}, []]}, 'block (type 3) end'),
    ({'LOOP': [{'ValBlockType': None}, [{'BR': 0}]]}, 'loop br 0 end'),
    ({'IF % % ELSE %': [{'ValBlockType': None}, ['NOP'], ['DROP']]}, 'if nop else drop end'),
    ({'IF % % ELSE %': [{'ValBlockType': None}, ['NOP'], []]}, 'if nop end'),
    ({'BR_IF': 2}, 'br_if 2'), ({'BR_TABLE': [[0, 1], 2]}, 'br_table 0 1 2'),
    ({'BR_ON_NULL': 1}, 'br_on_null 1'), ({'BR_ON_NON_NULL': 1}, 'br_on_non_null 1'),
    ({'BR_ON_CAST': [0, ref(True, 'AnyHT'), ref(False, 'StructHT')]}, 'br_on_cast 0 anyref (ref struct)'),
    ({'BR_ON_CAST_FAIL': [1, ref(False, 'EqHT'), ref(True, {'VarHT': {'StatX': 3}})]},
     'br_on_cast_fail 1 (ref eq) (ref null 3)'),
    ({'CALL': 4}, 'call 4'), ({'CALL_REF': 2}, 'call_ref 2'),
    ({'CALL_INDIRECT': [1, 2]}, 'call_indirect 1 (type 2)'),
    ({'RETURN_CALL': 4}, 'return_call 4'), ({'RETURN_CALL_REF': 2}, 'return_call_ref 2'),
    ({'RETURN_CALL_INDIRECT': [1, 2]}, 'return_call_indirect 1 (type 2)'),
    ({'THROW': 1}, 'throw 1'),
    ({'TRY_TABLE': [{'ValBlockType': None}, [{'Catch': [0, 1]}, {'CatchRef': [2, 3]}, {'CatchAll': 0},
                                              {'CatchAllRef': 1}], ['NOP']]},
     'try_table (catch 0 1) (catch_ref 2 3) (catch_all 0) (catch_all_ref 1) nop end'),
    ({'LOCAL.GET': 1}, 'local.get 1'), ({'LOCAL.SET': 1}, 'local.set 1'), ({'LOCAL.TEE': 1}, 'local.tee 1'),
    ({'GLOBAL.GET': 1}, 'global.get 1'), ({'GLOBAL.SET': 1}, 'global.set 1'),
    ({'TABLE.GET': 1}, 'table.get 1'), ({'TABLE.SET': 1}, 'table.set 1'), ({'TABLE.SIZE': 1}, 'table.size 1'),
    ({'TABLE.GROW': 1}, 'table.grow 1'), ({'TABLE.FILL': 1}, 'table.fill 1'),
    ({'TABLE.COPY': [1, 2]}, 'table.copy 1 2'), ({'TABLE.INIT': [1, 3]}, 'table.init 1 3'),
    ({'ELEM.DROP': 2}, 'elem.drop 2'), ({'MEMORY.SIZE': 1}, 'memory.size 1'),
    ({'MEMORY.GROW': 1}, 'memory.grow 1'), ({'MEMORY.FILL': 1}, 'memory.fill 1'),
    ({'MEMORY.COPY': [1, 2]}, 'memory.copy 1 2'), ({'MEMORY.INIT': [1, 3]}, 'memory.init 1 3'),
    ({'DATA.DROP': 2}, 'data.drop 2'), ({'REF.NULL': 'FuncHT'}, 'ref.null func'),
    ({'REF.NULL': 'NoExnHT'}, 'ref.null noexn'), ({'REF.NULL': {'VarHT': {'StatX': 3}}}, 'ref.null 3'),
    ({'REF.FUNC': 2}, 'ref.func 2'), ('REF.IS_NULL', 'ref.is_null'), ('REF.AS_NON_NULL', 'ref.as_non_null'),
    ({'REF.TEST': ref(False, {'VarHT': {'StatX': 3}})}, 'ref.test (ref 3)'),
    ({'REF.TEST': ref(True, 'AnyHT')}, 'ref.test anyref'),
    ({'REF.CAST': ref(False, 'I31HT')}, 'ref.cast (ref i31)'),
    ({'REF.CAST': ref(True, 'NoneHT')}, 'ref.cast nullref'),
    ('REF.EQ', 'ref.eq'), ('REF.I31', 'ref.i31'), ({'I31.GET': 'SX'}, 'i31.get_s'),
    ({'I31.GET': 'ZX'}, 'i31.get_u'),
    ({'STRUCT.NEW': [1, 'Explicit']}, 'struct.new 1'), ({'STRUCT.NEW': [1, 'Implicit']}, 'struct.new_default 1'),
    ({'STRUCT.GET': [1, 2, None]}, 'struct.get 1 2'), ({'STRUCT.GET': [1, 2, 'SX']}, 'struct.get_s 1 2'),
    ({'STRUCT.GET': [1, 2, 'ZX']}, 'struct.get_u 1 2'), ({'STRUCT.SET': [1, 2]}, 'struct.set 1 2'),
    ({'ARRAY.NEW': [1, 'Explicit']}, 'array.new 1'), ({'ARRAY.NEW': [1, 'Implicit']}, 'array.new_default 1'),
    ({'ARRAY.NEW_FIXED': [1, 3]}, 'array.new_fixed 1 3'), ({'ARRAY.NEW_DATA': [1, 2]}, 'array.new_data 1 2'),
    ({'ARRAY.NEW_ELEM': [1, 2]}, 'array.new_elem 1 2'), ({'ARRAY.GET': [1, None]}, 'array.get 1'),
    ({'ARRAY.GET': [1, 'SX']}, 'array.get_s 1'), ({'ARRAY.GET': [1, 'ZX']}, 'array.get_u 1'),
    ({'ARRAY.SET': 1}, 'array.set 1'), ('ARRAY.LEN', 'array.len'), ({'ARRAY.COPY': [1, 2]}, 'array.copy 1 2'),
    ({'ARRAY.FILL': 1}, 'array.fill 1'), ({'ARRAY.INIT_DATA': [1, 2]}, 'array.init_data 1 2'),
    ({'ARRAY.INIT_ELEM': [1, 2]}, 'array.init_elem 1 2'),
    ({'EXTERN.CONVERT': 'Internalize'}, 'any.convert_extern'),
    ({'EXTERN.CONVERT': 'Externalize'}, 'extern.convert_any'),
    ({'CONST': {'I32': 4294967295}}, 'i32.const -1'), ({'CONST': {'I32': 2147483648}}, 'i32.const -2147483648'),
    ({'CONST': {'I64': 18446744073709551615}}, 'i64.const -1'), ({'CONST': {'I64': 300}}, 'i64.const 300'),
    ({'CONST': {'F32': {'NEG': {'NORM': [4194304, -2]}}}}, 'f32.const -0.375'),
    ({'CONST': {'F32': {'POS': {'SUBNORM': 1}}}}, 'f32.const 0x1p-149'),
    ({'CONST': {'F32': {'NEG': {'SUBNORM': 0}}}}, 'f32.const -0'),
    ({'CONST': {'F32': {'POS': {'NAN': 1}}}}, 'f32.const nan:0x1'),
    ({'CONST': {'F64': {'NEG': 'INF'}}}, 'f64.const -inf'),
    ({'CONST': {'F64': {'POS': {'NORM': [0, 1023]}}}}, 'f64.const 0x1p1023'),
    ({'CONST': {'F64': {'POS': {'NAN': 1 << 51}}}}, 'f64.const nan'),
    ({'VEC.CONST': {'V128': (2 << 64) | 1}}, 'v128.const i64x2 1 2'),
    ({'VEC.BINARY': {'V128': {'I8x16': {'Shuffle': list(range(15, -1, -1))}}}},
     'i8x16.shuffle 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1 0'),
    ({'LOAD': [1, memop('I64T', None, 3, 1 << 40)]}, 'i64.load 1 offset=1099511627776 align=8'),
]


def wat2wasm(texts):
    """Assemble each module text with wasmtime.wat2wasm (parsing only, no validation)."""
    script = ('import json, sys, wasmtime\n'
              'print(json.dumps([wasmtime.wat2wasm(t).hex() for t in json.load(sys.stdin)]))')
    result = subprocess.run([str(WASMTIME_PYTHON), '-c', script], input=json.dumps(texts),
                            capture_output=True, text=True, check=True)
    return [bytes.fromhex(h) for h in json.loads(result.stdout)]


def assemble(texts):
    """Assemble `(module (func <text>))` for each instruction text."""
    return wat2wasm([f'(module (func {t}))' for t in texts])


def uleb_at(data, pos):
    value = shift = 0
    while True:
        byte = data[pos]
        pos += 1
        value |= (byte & 0x7F) << shift
        shift += 7
        if not byte & 0x80:
            return value, pos


def sections(binary):
    """(section id, payload) pairs after the module header."""
    assert binary[:8] == b'\x00asm\x01\x00\x00\x00', binary[:8]
    pos, out = 8, []
    while pos < len(binary):
        size, start = uleb_at(binary, pos + 1)
        out.append((binary[pos], binary[start:start + size]))
        pos = start + size
    assert pos == len(binary)
    return out


def first_body(binary):
    """Instruction bytes of the only function body, without locals and final end."""
    payload = dict(sections(binary))[10]
    _, pos = uleb_at(payload, 0)  # function count
    body_size, pos = uleb_at(payload, pos)
    assert payload[pos] == 0, 'test bodies have no locals'
    return payload[pos + 1:pos + body_size - 1]


# ---------------------------------------------------------------------------
# Whole modules. Each AST is paired with module text written from the AST's
# meaning, not from the encoder's bytes; wat2wasm assembles the text.

NUM_TEXT = {'I32T': 'i32', 'I64T': 'i64', 'F32T': 'f32', 'F64T': 'f64'}
ABS_TEXT = {'FuncHT': 'func', 'ExternHT': 'extern', 'AnyHT': 'any', 'EqHT': 'eq', 'I31HT': 'i31',
            'StructHT': 'struct', 'ArrayHT': 'array', 'ExnHT': 'exn', 'NoExnHT': 'noexn',
            'NoFuncHT': 'nofunc', 'NoExternHT': 'noextern', 'NoneHT': 'none'}


def name(text):
    return [ord(c) for c in text]


def reft(null, heap):
    return {'RefT': ref(null, heap)}


def subtype(final, supers, comp):
    return {'SubT': ['Final' if final else 'NoFinal', [{'VarHT': x} for x in supers], comp]}


def field(mut, storage):
    return {'FieldT': ['Var' if mut else 'Cons', storage]}


def struct(*fields):
    return {'DefStructT': {'StructT': list(fields)}}


def memtype(addrtype, low, high=None):
    return {'MemoryT': [addrtype, {'MIN': low, 'MAX': high}]}


def active(index, offset):
    return {'Active': {'INDEX': index, 'OFFSET': offset}}


def types_module():
    stat, rec = (lambda i: {'StatX': i}), (lambda i: {'RecX': i})
    nullable = [reft(True, h) for h in ABS_TEXT]
    i32_field = field(False, {'ValStorageT': I32})
    array_field = field(True, {'ValStorageT': reft(True, {'VarHT': rec(2)})})
    ast = module(TYPES=[
        functype([I32, I64, F32, F64, V128] + nullable,
                 [reft(False, 'FuncHT'), reft(False, {'VarHT': stat(0)}), reft(True, {'VarHT': stat(0)})]),
        {'RecT': [subtype(False, [], struct(i32_field, field(True, {'PackStorageT': 'I8'}),
                                            field(True, {'PackStorageT': 'I16'}),
                                            field(True, {'ValStorageT': reft(True, {'VarHT': rec(1)})}))),
                  subtype(True, [rec(0)], struct(i32_field))]},
        {'RecT': [subtype(False, [stat(1)], struct())]},
        {'RecT': [subtype(False, [], {'DefArrayT': {'ArrayT': array_field}}),
                  subtype(True, [rec(0)], {'DefArrayT': {'ArrayT': array_field}}),
                  subtype(True, [], {'DefFuncT': {'FuncT': [[reft(False, {'VarHT': rec(1)})],
                                                            [reft(True, {'VarHT': stat(3)})]]}})]},
        {'RecT': []},
        functype()])
    wat = '''(module
      (type (func (param i32 i64 f32 f64 v128 funcref externref anyref eqref i31ref structref
                         arrayref exnref nullexnref nullfuncref nullexternref nullref)
                  (result (ref func) (ref 0) (ref null 0))))
      (rec (type (sub (struct (field i32) (field (mut i8)) (field (mut i16)) (field (mut (ref null 2))))))
           (type (sub final 1 (struct (field i32)))))
      (type (sub 1 (struct)))
      (rec (type (sub (array (mut (ref null 6)))))
           (type (sub final 4 (array (mut (ref null 6)))))
           (type (func (param (ref 5)) (result (ref null 3)))))
      (rec)
      (type (func)))'''
    return ast, wat


def declarations_module():
    funcref = ref(True, 'FuncHT')
    s2 = {'VarHT': {'StatX': 2}}
    body = [{'BLOCK': [{'ValBlockType': reft(True, 'FuncHT')}, [{'REF.NULL': 'FuncHT'}]]},
            {'REF.FUNC': 2}, {'CONST': {'I32': 1}}, {'SELECT': [reft(True, 'FuncHT')]}, 'DROP',
            {'CONST': {'I32': 0}}, {'CONST': {'I32': 0}}, {'CONST': {'I32': 0}}, {'MEMORY.INIT': [1, 2]},
            {'DATA.DROP': 2}]
    ast = module(
        TYPES=[functype(), functype([I64]), {'RecT': [subtype(False, [], struct())]}],
        IMPORTS=[
            {'MODULENAME': name('env'), 'ITEMNAME': name('f'), 'IDESC': {'FuncImport': 0}},
            {'MODULENAME': name('é'), 'ITEMNAME': name('🦀'),
             'IDESC': {'TableImport': {'TableT': ['I64AT', {'MIN': 1, 'MAX': 1 << 40}, ref(True, s2)]}}},
            {'MODULENAME': name('m'), 'ITEMNAME': name('mem'), 'IDESC': {'MemImport': memtype('I64AT', 0, 65536)}},
            {'MODULENAME': name('m'), 'ITEMNAME': name('g'),
             'IDESC': {'GlobalImport': {'GlobalT': ['Var', reft(False, 'EqHT')]}}},
            {'MODULENAME': name('m'), 'ITEMNAME': name('tag'), 'IDESC': {'TagImport': 1}},
            {'MODULENAME': [], 'ITEMNAME': [], 'IDESC': {'FuncImport': 1}}],
        FUNCS=[{'FTYPE': 0, 'BODY': body,
                'LOCALS': [{'LTYPE': t} for t in (I32, I32, F64, I32, reft(True, 'FuncHT'),
                                                  reft(True, 'FuncHT'), V128, reft(True, s2))]},
               {'FTYPE': 1, 'LOCALS': [], 'BODY': []}],
        TABLES=[{'TTYPE': {'TableT': ['I32AT', {'MIN': 0, 'MAX': None}, funcref]}, 'TINIT': [{'REF.FUNC': 2}]},
                {'TTYPE': {'TableT': ['I64AT', {'MIN': 3, 'MAX': 3}, ref(True, s2)]}, 'TINIT': [{'REF.NULL': s2}]}],
        MEMS=[{'MTYPE': memtype('I32AT', 127, 128)}, {'MTYPE': memtype('I32AT', 1)},
              {'MTYPE': memtype('I64AT', 1 << 40)}],
        TAGS=[{'TGTYPE': 1}],
        GLOBALS=[{'GTYPE': {'GlobalT': ['Var', I32]}, 'GINIT': [{'CONST': {'I32': 0xFFFFFFFF}}]},
                 {'GTYPE': {'GlobalT': ['Cons', reft(True, 'FuncHT')]}, 'GINIT': [{'REF.FUNC': 3}]},
                 {'GTYPE': {'GlobalT': ['Cons', I64]},
                  'GINIT': [{'CONST': {'I64': 1}}, {'CONST': {'I64': 2}}, {'BINOP': {'I64': 'IAdd'}}]},
                 {'GTYPE': {'GlobalT': ['Cons', reft(False, s2)]}, 'GINIT': [{'STRUCT.NEW': [2, 'Implicit']}]}],
        EXPORTS=[{'NAME': name('f'), 'EDESC': {'FuncExport': 3}}, {'NAME': name('t'), 'EDESC': {'TableExport': 2}},
                 {'NAME': name('m'), 'EDESC': {'MemExport': 3}}, {'NAME': name('g'), 'EDESC': {'GlobalExport': 4}},
                 {'NAME': name('ü'), 'EDESC': {'TagExport': 1}}],
        START={'SFUNC': 2},
        ELEMS=[{'ETYPE': funcref, 'EINIT': [[{'REF.FUNC': 2}], [{'REF.NULL': 'FuncHT'}]],
                'EMODE': active(1, [{'CONST': {'I32': 1}}])},
               {'ETYPE': ref(True, s2), 'EINIT': [[{'STRUCT.NEW': [2, 'Implicit']}]],
                'EMODE': active(2, [{'CONST': {'I64': 2}}])},
               {'ETYPE': ref(False, 'FuncHT'), 'EINIT': [[{'REF.FUNC': 3}]], 'EMODE': 'Passive'},
               {'ETYPE': funcref, 'EINIT': [], 'EMODE': 'Passive'},
               {'ETYPE': funcref, 'EINIT': [[{'REF.FUNC': 2}]], 'EMODE': 'Declarative'},
               {'ETYPE': funcref, 'EINIT': [[{'REF.FUNC': 3}]], 'EMODE': active(0, [{'CONST': {'I64': 0}}])}],
        DATAS=[{'DINIT': 'é🦀', 'DMODE': active(0, [{'CONST': {'I64': 8}}])},
               {'DINIT': '', 'DMODE': active(3, [{'CONST': {'I64': 1 << 40}}])},
               {'DINIT': 'x' * 200, 'DMODE': 'Passive'}])
    wat = '''(module
      (type (func))
      (type (func (param i64)))
      (type (sub (struct)))
      (import "env" "f" (func (type 0)))
      (import "é" "🦀" (table i64 1 1099511627776 (ref null 2)))
      (import "m" "mem" (memory i64 0 65536))
      (import "m" "g" (global (mut (ref eq))))
      (import "m" "tag" (tag (type 1)))
      (import "" "" (func (type 1)))
      (func (type 0) (local i32 i32 f64 i32 funcref funcref v128 (ref null 2))
        block (result funcref) ref.null func end
        ref.func 2 i32.const 1 select (result funcref) drop
        i32.const 0 i32.const 0 i32.const 0 memory.init 1 2
        data.drop 2)
      (func (type 1))
      (table 0 funcref (ref.func 2))
      (table i64 3 3 (ref null 2) (ref.null 2))
      (memory 127 128)
      (memory 1)
      (memory i64 1099511627776)
      (tag (type 1))
      (global (mut i32) (i32.const -1))
      (global funcref (ref.func 3))
      (global i64 (i64.add (i64.const 1) (i64.const 2)))
      (global (ref 2) (struct.new_default 2))
      (export "f" (func 3))
      (export "t" (table 2))
      (export "m" (memory 3))
      (export "g" (global 4))
      (export "ü" (tag 1))
      (start 2)
      (elem (table 1) (offset i32.const 1) funcref (item ref.func 2) (item ref.null func))
      (elem (table 2) (offset i64.const 2) (ref null 2) (item struct.new_default 2))
      (elem (ref func) (item ref.func 3))
      (elem funcref)
      (elem declare funcref (item ref.func 2))
      (elem (table 0) (offset i64.const 0) funcref (item ref.func 3))
      (data (memory 0) (offset i64.const 8) "é🦀")
      (data (memory 3) (offset i64.const 1099511627776) "")
      (data "''' + 'x' * 200 + '''"))'''
    return ast, wat


U32_EDGES = [0, 1, 63, 64, 127, 128, 16383, 16384, 65536, 2**31 - 1, 2**31, 2**32 - 1]
U64_EDGES = U32_EDGES + [2**32, 2**53, 2**63 - 1, 2**63, 2**64 - 1]
CODE_POINTS = [(0x20, 0x7E), (0x80, 0x7FF), (0x800, 0xD7FF), (0xE000, 0xFFFF), (0x10000, 0x10FFFF)]


def random_index(rng, scope):
    total, base, size = scope
    if rng.random() < 0.5:
        i = rng.randrange(total)
        return {'StatX': i}, str(i)
    j = rng.randrange(size)
    return {'RecX': j}, str(base + j)


def random_valtype(rng, scope):
    roll = rng.random()
    if roll < 0.4:
        t = rng.choice(list(NUM_TEXT))
        return {'NumT': t}, NUM_TEXT[t]
    if roll < 0.5:
        return V128, 'v128'
    null = 'null ' if rng.random() < 0.5 else ''
    if rng.random() < 0.5:
        heap = rng.choice(list(ABS_TEXT))
        text = ABS_TEXT[heap]
    else:
        index, text = random_index(rng, scope)
        heap = {'VarHT': index}
    return reft(bool(null), heap), f'(ref {null}{text})'


def random_fieldtype(rng, scope):
    if rng.random() < 0.3:
        pack = rng.choice(['I8', 'I16'])
        storage, text = {'PackStorageT': pack}, pack.lower()
    else:
        valtype, text = random_valtype(rng, scope)
        storage = {'ValStorageT': valtype}
    mut = rng.random() < 0.5
    return field(mut, storage), f'(mut {text})' if mut else text


def random_comptype(rng, scope):
    roll = rng.random()
    if roll < 0.4:
        params = [random_valtype(rng, scope) for _ in range(rng.randint(0, 3))]
        results = [random_valtype(rng, scope) for _ in range(rng.randint(0, 3))]
        text = ''.join(f' (param {t})' for _, t in params) + ''.join(f' (result {t})' for _, t in results)
        return {'DefFuncT': {'FuncT': [[a for a, _ in params], [a for a, _ in results]]}}, f'(func{text})'
    if roll < 0.8:
        fields = [random_fieldtype(rng, scope) for _ in range(rng.randint(0, 3))]
        return struct(*[a for a, _ in fields]), '(struct' + ''.join(f' (field {t})' for _, t in fields) + ')'
    fieldtype, text = random_fieldtype(rng, scope)
    return {'DefArrayT': {'ArrayT': fieldtype}}, f'(array {text})'


def random_types(rng):
    sizes = [rng.randint(0, 3) for _ in range(rng.randint(1, 5))]
    total, base, ast, wat = max(sum(sizes), 1), 0, [], []
    for size in sizes:
        scope = (total, base, size)
        subs, texts = [], []
        for _ in range(size):
            final = rng.random() < 0.5
            supers, super_text = [], ''
            if rng.random() < 0.5:
                index, text = random_index(rng, scope)
                supers, super_text = [index], ' ' + text
            comp, comp_text = random_comptype(rng, scope)
            subs.append(subtype(final, supers, comp))
            if final and not supers:
                texts.append(f'(type {comp_text})')
            else:
                texts.append(f'(type (sub{" final" if final else ""}{super_text} {comp_text}))')
        ast.append({'RecT': subs})
        wat.append(texts[0] if size == 1 else '(rec ' + ' '.join(texts) + ')')
        base += size
    return ast, wat


def random_limits(rng, addrtype):
    edges = U64_EDGES if addrtype == 'I64AT' else U32_EDGES
    low = rng.choice(edges)
    high = rng.choice(edges) if rng.random() < 0.5 else None
    text = ('i64 ' if addrtype == 'I64AT' else '') + str(low) + ('' if high is None else f' {high}')
    return {'MIN': low, 'MAX': high}, text


def random_name(rng):
    chars = [rng.randint(*rng.choice(CODE_POINTS)) for _ in range(rng.randint(0, 6))]
    return chars, '"' + ''.join(f'\\u{{{c:x}}}' for c in chars) + '"'


def random_float(rng, width):
    """A float magnitude and its hexadecimal text, written from the magnitude's definition."""
    mant, emin, emax = (23, -126, 127) if width == 32 else (52, -1022, 1023)
    digits = (mant + 3) // 4
    shift = digits * 4 - mant
    sign = rng.choice(['POS', 'NEG'])
    roll = rng.random()
    if roll < 0.5:
        m, e = rng.randrange(1 << mant), rng.randint(emin, emax)
        mag, text = {'NORM': [m, e]}, f'0x1.{m << shift:0{digits}x}p{e}'
    elif roll < 0.7:
        m = rng.randrange(1 << mant)
        mag, text = {'SUBNORM': m}, f'0x0.{m << shift:0{digits}x}p{emin}'
    elif roll < 0.8:
        mag, text = 'INF', 'inf'
    else:
        m = rng.randrange(1, 1 << mant)
        mag, text = {'NAN': m}, f'nan:0x{m:x}'
    return {sign: mag}, ('-' if sign == 'NEG' else '') + text


def random_global(rng):
    kind = rng.choice(['I32', 'I64', 'F32', 'F64'])
    if kind in ('I32', 'I64'):
        bits = int(kind[1:])
        value = rng.choice(U32_EDGES if bits == 32 else U64_EDGES)
        value = value if rng.random() < 0.5 else rng.randrange(1 << bits)
        signed = value - (1 << bits) if value >= 1 << (bits - 1) else value
        const, text = value, str(signed)
    else:
        const, text = random_float(rng, int(kind[1:]))
    return ({'GTYPE': {'GlobalT': ['Cons', {'NumT': kind + 'T'}]}, 'GINIT': [{'CONST': {kind: const}}]},
            f'(global {kind.lower()} ({kind.lower()}.const {text}))')


def random_module(rng):
    types, texts = random_types(rng)
    imports, tables, mems, globals_ = [], [], [], []
    for _ in range(rng.randint(0, 3)):
        (module_name, module_text), (item_name, item_text) = random_name(rng), random_name(rng)
        imports.append({'MODULENAME': module_name, 'ITEMNAME': item_name,
                        'IDESC': {'GlobalImport': {'GlobalT': ['Cons', I32]}}})
        texts.append(f'(import {module_text} {item_text} (global i32))')
    for _ in range(rng.randint(0, 2)):
        addrtype = rng.choice(['I32AT', 'I64AT'])
        lim, text = random_limits(rng, addrtype)
        tables.append({'TTYPE': {'TableT': [addrtype, lim, ref(True, 'FuncHT')]}, 'TINIT': [{'REF.NULL': 'FuncHT'}]})
        texts.append(f'(table {text} funcref (ref.null func))')
    for _ in range(rng.randint(0, 2)):
        addrtype = rng.choice(['I32AT', 'I64AT'])
        lim, text = random_limits(rng, addrtype)
        mems.append({'MTYPE': {'MemoryT': [addrtype, lim]}})
        texts.append(f'(memory {text})')
    for _ in range(rng.randint(0, 4)):
        glob, text = random_global(rng)
        globals_.append(glob)
        texts.append(text)
    ast = module(TYPES=types, IMPORTS=imports, TABLES=tables, MEMS=mems, GLOBALS=globals_)
    return ast, '(module ' + ' '.join(texts) + ')'


class GoldenTests(unittest.TestCase):
    def test_empty_module(self):
        self.assertEqual(enc.encode_module(module()), b'\x00asm\x01\x00\x00\x00')

    def test_start_function_module(self):
        m = module(TYPES=[functype()],
                   FUNCS=[{'FTYPE': 0, 'LOCALS': [{'LTYPE': I32}, {'LTYPE': I32}, {'LTYPE': F64}],
                           'BODY': ['UNREACHABLE']}],
                   START={'SFUNC': 0})
        self.assertEqual(enc.encode_module(m).hex(),
                         '0061736d01000000'
                         '010401600000'          # type section: (func)
                         '03020100'              # function section
                         '080100'                # start 0
                         '0a09010702027f017c000b')  # code: locals 2xi32 1xf64; unreachable

    def test_recursive_group_resolves_recx_to_absolute_index(self):
        node = {'SubT': ['NoFinal', [], {'DefStructT': {'StructT': [
            {'FieldT': ['Cons', {'ValStorageT': {'RefT': ref(True, {'VarHT': {'RecX': 1}})}}]}]}}]}
        child = {'SubT': ['Final', [{'VarHT': {'RecX': 0}}], {'DefStructT': {'StructT': []}}]}
        m = module(TYPES=[functype(), {'RecT': [node, child]}])
        # group 2 starts at absolute index 1: RecX 1 -> 2, RecX 0 -> 1
        self.assertEqual(enc.encode_module(m)[8:].hex(),
                         '011202' '600000' '4e02' '50005f01630200' '4f01015f00')

    def test_data_segment_uses_utf8_and_data_count(self):
        m = module(MEMS=[{'MTYPE': {'MemoryT': ['I32AT', {'MIN': 1, 'MAX': None}]}}],
                   DATAS=[{'DINIT': 'é', 'DMODE': {'Active': {'INDEX': 0, 'OFFSET': [{'CONST': {'I32': 8}}]}}}])
        self.assertEqual(enc.encode_module(m)[8:].hex(),
                         '050301' '0001'                # memory 1 page
                         '0c0101'                       # data count 1
                         '0b0801' '00' '41080b' '02c3a9')  # active mem 0, offset 8, "é"

    def test_float_bits(self):
        self.assertEqual(enc.float_bits({'POS': {'NAN': 1 << 22}}, 32, 't'), 0x7FC00000)
        self.assertEqual(enc.float_bits({'NEG': {'NORM': [0, 0]}}, 64, 't'), 0xBFF0000000000000)


class UnencodableTests(unittest.TestCase):
    def assertUnencodable(self, value):
        with self.assertRaises(enc.Unencodable):
            instr(value)

    def test_out_of_range_values(self):
        self.assertUnencodable({'CONST': {'I32': 1 << 32}})
        self.assertUnencodable({'CONST': {'I64': 1 << 64}})
        self.assertUnencodable({'LOCAL.GET': 1 << 32})
        self.assertUnencodable({'LOAD': [0, memop('I32T', None, 64, 0)]})
        self.assertUnencodable({'LOAD': [0, memop('I32T', None, 0, 1 << 64)]})
        self.assertUnencodable({'VEC.LOAD_LANE': [0, memop('V128T', 'I8', 0, 0), -1]})

    def test_non_canonical_floats(self):
        self.assertUnencodable({'CONST': {'F32': {'POS': {'NORM': [1 << 23, 0]}}}})
        self.assertUnencodable({'CONST': {'F32': {'POS': {'NORM': [0, 128]}}}})
        self.assertUnencodable({'CONST': {'F32': {'POS': {'NAN': 0}}}})

    def test_shapes_without_opcodes(self):
        self.assertUnencodable({'VEC.UNARY': {'V128': {'I32x4': 'Popcnt'}}})
        self.assertUnencodable({'VEC.COMPARE': {'V128': {'I64x2': 'LtU'}}})
        self.assertUnencodable({'VEC.BINARY': {'V128': {'I8x16': {'Shuffle': [0, 1]}}}})
        self.assertUnencodable({'LOAD': [0, memop('F32T', ['I8', 'SX'])]})

    def test_runtime_only_types_and_free_recx(self):
        self.assertUnencodable({'REF.NULL': 'BotHT'})
        self.assertUnencodable({'REF.NULL': {'VarHT': {'RecX': 0}}})
        self.assertUnencodable({'SELECT': ['BotT']})


@unittest.skipUnless(WASMTIME_PYTHON.exists(), 'implementations/local/wasmtime-venv is not installed')
class OpcodeCrossCheckTests(unittest.TestCase):
    def test_every_opcode_table_entry_matches_the_text_assembler(self):
        cases = list(opcode_cases()) + STRUCTURED_CASES
        expected = assemble([text for _, text in cases])
        for (value, text), binary in zip(cases, expected):
            with self.subTest(text=text):
                self.assertEqual(instr(value).hex(), first_body(binary).hex())


@unittest.skipUnless(WASMTIME_PYTHON.exists(), 'implementations/local/wasmtime-venv is not installed')
class ModuleCrossCheckTests(unittest.TestCase):
    """Whole modules match wat2wasm byte for byte, apart from the data count section.

    wat2wasm emits the data count section only when an instruction needs it;
    the encoder always emits it with data segments, so it is checked
    separately and removed before comparison.
    """

    def assertSameModules(self, pairs):
        expected = wat2wasm([text for _, text in pairs])
        for n, ((ast, text), reference) in enumerate(zip(pairs, expected)):
            with self.subTest(case=n, text=text[:200]):
                ours = sections(enc.encode_module(ast))
                datacount = [payload for sid, payload in ours if sid == 12]
                self.assertEqual(datacount, [enc.u32(len(ast['DATAS']))] if ast['DATAS'] else [])
                self.assertEqual([(sid, payload.hex()) for sid, payload in ours if sid != 12],
                                 [(sid, payload.hex()) for sid, payload in sections(reference) if sid != 12])

    def test_every_section_kind(self):
        self.assertSameModules([types_module(), declarations_module()])

    def test_random_types_limits_names_and_constants(self):
        rng = random.Random(20261111)
        self.assertSameModules([random_module(rng) for _ in range(400)])


if __name__ == '__main__':
    unittest.main()
