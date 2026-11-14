"""Positive and negative integration checks against the real Module_ok relation."""
from __future__ import annotations

import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest

from experiments.wasm.check import check_modules
from scripts.toolchain import PROJECT


class ModuleOracleTests(unittest.TestCase):
    def test_module_validation_and_malformed_input(self) -> None:
        empty: dict[str, object] = {name: [] for name in (
            'TYPES', 'GLOBALS', 'TABLES', 'MEMS', 'TAGS', 'FUNCS', 'ELEMS', 'DATAS', 'IMPORTS', 'EXPORTS')}
        empty['START'] = None
        function_type: object = {'RecT': [{'SubT': ['Final', [],
            {'DefFuncT': {'FuncT': [[], [{'NumT': 'I32T'}]]}}]}]}
        function: dict[str, object] = {'FTYPE': 0, 'LOCALS': [], 'BODY': [{'CONST': {'I32': 7}}]}
        valid: dict[str, object] = empty | {'TYPES': [function_type], 'FUNCS': [function]}
        unicode_data: dict[str, object] = empty | {
            'DATAS': [{'DINIT': '\u0085\u2028\u2029', 'DMODE': 'Passive'}]}
        wrong_result: dict[str, object] = valid | {'FUNCS': [function | {'BODY': []}]}
        wrong_type: dict[str, object] = valid | {'FUNCS': [function | {'FTYPE': 1}]}
        wrong_local: dict[str, object] = valid | {'FUNCS': [function | {'BODY': [{'LOCAL.GET': 0}]}]}
        wrong_export: dict[str, object] = valid | {'EXPORTS': [{'NAME': [102], 'EDESC': {'FuncExport': 1}}]}
        wrong_start: dict[str, object] = valid | {'START': {'SFUNC': 0}}
        with tempfile.TemporaryDirectory(dir=PROJECT / 'build/wasm') as temporary:
            path: Path = Path(temporary) / 'modules.jsonl'
            path.write_text('\n'.join(json.dumps(value, ensure_ascii=False) for value in (
                empty, valid, unicode_data, wrong_result, wrong_type, wrong_local, wrong_export, wrong_start)) + '\n')
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(check_modules(path), [True, True, True, False, False, False, False, False])
            path.write_text(json.dumps(empty | {'TYPES': ['UnknownConstructor']}) + '\n')
            with self.assertRaisesRegex(ChildProcessError, 'unknown constructor'):
                check_modules(path)


if __name__ == '__main__':
    unittest.main()
