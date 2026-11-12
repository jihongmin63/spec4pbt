"""End-to-end classification of implementations/wasm_adapter.py on real engines.

Each test sends a protocol request for Module_ok or Module_init_ok and checks
the status and that the response passes the runner's wire validation. Tests
for an engine are skipped unless it is installed under implementations/local.
"""
import json
import os
import subprocess
import sys
import unittest

from scripts.property.protocol import validate_response
from scripts.tests import ROOT
from scripts.tests.test_wasm_encoder import F64, I32, I64, functype, memop, module, ref

ADAPTER = ROOT / 'implementations/wasm_adapter.py'
WASMTIME_PYTHON = ROOT / 'implementations/local/wasmtime-venv/bin/python'
NODE = ROOT / 'implementations/local/node/node-v26.13.0-linux-x64/bin/node'
ENGINES = {'wasmtime': (WASMTIME_PYTHON, WASMTIME_PYTHON.exists()),
           'node': (sys.executable, NODE.exists())}


def call(engine, relation, value, timeout=None):
    request = {'plan_id': 'plan', 'case_id': '0', 'occurrence_id': 'call-0', 'relation_id': relation,
               'input': [value], 'observe': []}
    env = dict(os.environ)
    if timeout is not None:
        env['SPEC4PBT_WASM_TIMEOUT'] = str(timeout)
    python, _ = ENGINES[engine]
    result = subprocess.run([str(python), str(ADAPTER), engine], input=json.dumps(request),
                            capture_output=True, text=True, timeout=120, env=env, check=True)
    return validate_response(json.loads(result.stdout), request)


def mem(addrtype, low, high=None):
    return {'MTYPE': {'MemoryT': [addrtype, {'MIN': low, 'MAX': high}]}}


def start_module(body, **fields):
    types = fields.pop('TYPES', [functype()])
    funcs = [{'FTYPE': 0, 'LOCALS': [], 'BODY': body}] + fields.pop('FUNCS', [])
    return module(TYPES=types, FUNCS=funcs, START={'SFUNC': 0}, **fields)


def kitchen_sink():
    """A valid module touching every section encoder and most Wasm 3.0 features."""
    point = {'SubT': ['NoFinal', [], {'DefStructT': {'StructT': [
        {'FieldT': ['Var', {'ValStorageT': I32}]},
        {'FieldT': ['Cons', {'ValStorageT': {'RefT': ref(True, {'VarHT': {'RecX': 1}})}}]}]}}]}
    bytes_ = {'SubT': ['Final', [], {'DefArrayT': {'ArrayT': {'FieldT': ['Var', {'PackStorageT': 'I8'}]}}}]}
    types = [functype(), {'RecT': [point, bytes_]}, functype([I32], [I32]), functype([I64])]
    funcref = ref(True, 'FuncHT')
    body = [
        {'CONST': {'I32': 0}}, {'CONST': {'I32': 0}}, {'CONST': {'I32': 1}}, {'MEMORY.INIT': [0, 1]},
        {'DATA.DROP': 1},
        {'CONST': {'I64': 8}}, {'LOAD': [1, memop('I64T', None, 3, 0)]}, 'DROP',
        {'CONST': {'I32': 5}}, {'REF.NULL': {'VarHT': {'StatX': 2}}},
        {'STRUCT.NEW': [1, 'Explicit']}, {'STRUCT.GET': [1, 0, None]}, 'DROP',
        {'BLOCK': [{'ValBlockType': I64}, [
            {'TRY_TABLE': [{'ValBlockType': None}, [{'Catch': [0, 0]}],
                           [{'CONST': {'I64': 3}}, {'THROW': 0}]]},
            'UNREACHABLE']]}, 'DROP',
        {'CONST': {'I32': 7}}, {'CALL': 1}, 'DROP',
        {'VEC.CONST': {'V128': 1}}, {'VEC.TEST': {'V128': {'I8x16': 'AllTrue'}}}, 'DROP',
    ]
    return module(
        TYPES=types,
        FUNCS=[{'FTYPE': 0, 'LOCALS': [{'LTYPE': F64}], 'BODY': body},
               {'FTYPE': 3, 'LOCALS': [], 'BODY': [{'LOCAL.GET': 0}, {'RETURN_CALL': 2}]},
               {'FTYPE': 3, 'LOCALS': [], 'BODY': [{'LOCAL.GET': 0}]}],
        TABLES=[{'TTYPE': {'TableT': ['I64AT', {'MIN': 2, 'MAX': 4}, funcref]}, 'TINIT': [{'REF.NULL': 'FuncHT'}]}],
        MEMS=[mem('I32AT', 1, 2), mem('I64AT', 1)],
        TAGS=[{'TGTYPE': 4}],
        GLOBALS=[{'GTYPE': {'GlobalT': ['Var', I32]}, 'GINIT': [{'CONST': {'I32': 1}}]},
                 {'GTYPE': {'GlobalT': ['Cons', {'RefT': funcref}]}, 'GINIT': [{'REF.FUNC': 2}]}],
        EXPORTS=[{'NAME': [ord(c) for c in 'run'], 'EDESC': {'FuncExport': 0}},
                 {'NAME': [ord(c) for c in 'mem'], 'EDESC': {'MemExport': 1}},
                 {'NAME': [ord(c) for c in 'tag'], 'EDESC': {'TagExport': 0}}],
        START={'SFUNC': 0},
        ELEMS=[{'ETYPE': funcref, 'EINIT': [[{'REF.FUNC': 1}]],
                'EMODE': {'Active': {'INDEX': 0, 'OFFSET': [{'CONST': {'I64': 1}}]}}},
               {'ETYPE': funcref, 'EINIT': [[{'REF.FUNC': 2}]], 'EMODE': 'Passive'},
               {'ETYPE': funcref, 'EINIT': [[{'REF.FUNC': 2}]], 'EMODE': 'Declarative'}],
        DATAS=[{'DINIT': 'hi', 'DMODE': {'Active': {'INDEX': 0, 'OFFSET': [{'CONST': {'I32': 16}}]}}},
               {'DINIT': 'x', 'DMODE': 'Passive'}])


class AdapterCases:
    engine = None

    def assertStatus(self, relation, value, status, timeout=None):
        response = call(self.engine, relation, value, timeout)
        self.assertEqual(response['status'], status, response)
        return response

    def test_valid_module_validates_and_instantiates(self):
        m = kitchen_sink()
        self.assertStatus('Module_ok', m, 'success')
        self.assertStatus('Module_init_ok', m, 'success')

    def test_validation_error(self):
        m = module(TYPES=[functype([], [I32])], FUNCS=[{'FTYPE': 0, 'LOCALS': [], 'BODY': []}])
        self.assertStatus('Module_ok', m, 'relation_failure')
        self.assertStatus('Module_init_ok', m, 'relation_failure')

    def test_start_trap_and_uncaught_exception(self):
        trap = start_module(['UNREACHABLE'])
        self.assertStatus('Module_ok', trap, 'success')
        self.assertStatus('Module_init_ok', trap, 'relation_failure')
        throw = start_module([{'CONST': {'I64': 1}}, {'THROW': 0}],
                             TYPES=[functype(), functype([I64])], TAGS=[{'TGTYPE': 1}])
        self.assertStatus('Module_init_ok', throw, 'relation_failure')

    def test_missing_import_is_a_link_failure(self):
        m = module(TYPES=[functype()], IMPORTS=[{'MODULENAME': [109], 'ITEMNAME': [102],
                                                 'IDESC': {'FuncImport': 0}}])
        self.assertStatus('Module_ok', m, 'success')
        self.assertStatus('Module_init_ok', m, 'relation_failure')

    def test_resource_exhaustion_and_timeout_abort(self):
        recursion = start_module([{'CALL': 0}])
        self.assertStatus('Module_init_ok', recursion, 'abort')
        spin = start_module([{'LOOP': [{'ValBlockType': None}, [{'BR': 0}]]}])
        self.assertIn('timeout', self.assertStatus('Module_init_ok', spin, 'abort', timeout=1)['message'])

    def test_unencodable_module_aborts(self):
        m = start_module([{'CONST': {'I32': 1 << 40}}, 'DROP'])
        self.assertIn('unencodable', self.assertStatus('Module_ok', m, 'abort')['message'])

    def test_memory64_effective_address_does_not_wrap(self):
        def probe(address, offset):
            return start_module([{'CONST': {'I64': address}},
                                 {'LOAD': [0, memop('I32T', None, 0, offset)]}, 'DROP'],
                                MEMS=[mem('I64AT', 1)])
        self.assertStatus('Module_init_ok', probe(65532, 0), 'success')
        self.assertStatus('Module_init_ok', probe(65533, 0), 'relation_failure')
        self.assertStatus('Module_init_ok', probe((1 << 64) - 4, 4), 'relation_failure')


@unittest.skipUnless(ENGINES['wasmtime'][1], 'implementations/local/wasmtime-venv is not installed')
class WasmtimeAdapterTests(AdapterCases, unittest.TestCase):
    engine = 'wasmtime'

    def test_engine_specific_limits(self):
        self.assertStatus('Module_ok', module(MEMS=[mem('I64AT', 300_000)]), 'success')
        self.assertStatus('Module_ok', module(MEMS=[mem('I32AT', 0)] * 101), 'abort')


@unittest.skipUnless(ENGINES['node'][1], 'implementations/local/node is not installed')
class NodeAdapterTests(AdapterCases, unittest.TestCase):
    engine = 'node'

    def test_engine_specific_limits(self):
        self.assertStatus('Module_ok', module(MEMS=[mem('I64AT', 300_000)]), 'abort')
        self.assertStatus('Module_ok', module(MEMS=[mem('I32AT', 0)] * 101), 'success')


if __name__ == '__main__':
    unittest.main()
