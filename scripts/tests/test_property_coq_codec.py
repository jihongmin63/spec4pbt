"""Execute generated Coq codecs and compare their wire values with the AL bridge."""
import importlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from scripts.property.bridge import build_bridge
from scripts.property.codec import CodecError, decode_input


ROOT = Path(__file__).resolve().parents[2]
SCHEMA = {
    'tree': {'coq_type': 'CoqTree', 'constructors': [
        {'name': 'LEAF', 'coq_name': 'CoqLeaf', 'fields': ['nat', 'int', 'text', 'bool']},
        {'name': 'NODE', 'coq_name': 'CoqNode', 'fields': ['tree', 'tree']}]},
    'left': {'coq_type': 'CoqLeft', 'constructors': [
        {'name': 'STOP', 'coq_name': 'CoqStop', 'fields': []},
        {'name': 'LEFT', 'coq_name': 'CoqLeftNext', 'fields': ['right']}]},
    'right': {'coq_type': 'CoqRight', 'constructors': [
        {'name': 'RIGHT', 'coq_name': 'CoqRightNext', 'fields': ['left', 'tree']}]},
}
FIELDS = [
    {'name': 'count', 'type': 'nat'},
    {'name': 'debt', 'type': 'int'},
    {'name': 'message', 'type': 'text'},
    {'name': 'enabled', 'type': 'bool'},
    {'name': 'value', 'type': 'tree'},
    {'name': 'chain', 'type': 'left'},
]


def coq_text(text):
    """Build the test value from bytes independently of the production renderer."""
    result = 'EmptyString'
    for byte in reversed(text.encode('utf-8')):
        result = f'(String (ascii_of_nat {byte}) {result})'
    return result


class CoqCodecTests(unittest.TestCase):
    def codec(self):
        try:
            module = importlib.import_module('scripts.property.coq_codec')
        except ModuleNotFoundError:
            self.fail('typed Input Coq codec renderer is missing')
        return module

    def test_constructor_metadata_drives_strict_python_decoder(self):
        codec = self.codec()
        constructors = codec.constructor_schema(SCHEMA)
        wire = {'value': {'type': 'tree', 'constructor': 'LEAF', 'args': [
            {'type': 'nat', 'value': '4'}, {'type': 'int', 'value': '-7'},
            {'type': 'text', 'value': 'hi'}, {'type': 'bool', 'value': True}]}}
        self.assertEqual(decode_input(wire, FIELDS[4:5], constructors), wire)
        wire['value']['args'][0]['type'] = 'int'
        with self.assertRaises(CodecError):
            decode_input(wire, FIELDS[4:5], constructors)

    def test_rejects_incomplete_or_ambiguous_schema(self):
        codec = self.codec()
        malformed = [
            {'tree': {'coq_type': 'CoqTree', 'constructors': [
                {'name': 'LEAF', 'coq_name': 'CoqLeaf', 'fields': ['missing']}]}},
            {'tree': {'coq_type': 'CoqTree', 'constructors': [
                {'name': 'LEAF', 'coq_name': 'CoqLeaf', 'fields': []},
                {'name': 'LEAF', 'coq_name': 'CoqNode', 'fields': []}]}},
            {'tree': {'coq_type': 'CoqTree. Abort.', 'constructors': []}},
        ]
        for schema in malformed:
            with self.subTest(schema=schema), self.assertRaises(CodecError):
                codec.render_input_codec(FIELDS[4:5], schema)
        with self.assertRaises(CodecError):
            codec.render_input_codec([{'name': 'x', 'type': 'missing'}], {})
        with self.assertRaises(CodecError):
            codec.render_input_codec([{'name': 'x', 'type': 'nat'},
                                      {'name': 'x', 'type': 'nat'}], {})

    def test_extracted_nested_and_mutual_values_roundtrip_through_bridge(self):
        codec = self.codec()
        checks = ROOT / '_opam-testing-theorems/checks'
        checks.mkdir(parents=True, exist_ok=True)
        run = Path(tempfile.mkdtemp(prefix='property-coq-codec.', dir=checks))
        text = 'quote " slash \\ controls ' + ''.join(map(chr, range(32))) + ' 한글 😀'
        leaf = {'type': 'tree', 'constructor': 'LEAF', 'args': [
            {'type': 'nat', 'value': '12'},
            {'type': 'int', 'value': '-123456789012345678901234567890'},
            {'type': 'text', 'value': text}, {'type': 'bool', 'value': True}]}
        node = {'type': 'tree', 'constructor': 'NODE', 'args': [leaf, leaf]}
        expected = {
            'count': {'type': 'nat', 'value': '0'},
            'debt': {'type': 'int', 'value': '123456789012345678901234567890'},
            'message': {'type': 'text', 'value': text},
            'enabled': {'type': 'bool', 'value': False},
            'value': node,
            'chain': {'type': 'left', 'constructor': 'LEFT', 'args': [
                {'type': 'right', 'constructor': 'RIGHT', 'args': [
                    {'type': 'left', 'constructor': 'STOP', 'args': []}, node]}]},
        }
        probe = '''From Coq Require Import String Ascii Bool ZArith.
Open Scope string_scope.
Inductive CoqTree : Set :=
| CoqLeaf : nat -> Z -> string -> bool -> CoqTree
| CoqNode : CoqTree -> CoqTree -> CoqTree.
Inductive CoqLeft : Set := CoqStop : CoqLeft | CoqLeftNext : CoqRight -> CoqLeft
with CoqRight : Set := CoqRightNext : CoqLeft -> CoqTree -> CoqRight.
Record Input := mkInput {
  input_count : nat; input_debt : Z; input_message : string;
  input_enabled : bool; input_value : CoqTree; input_chain : CoqLeft
}.
Inductive predicate : Input -> Prop := precondition : forall i, predicate i.
''' + codec.render_input_codec(FIELDS, SCHEMA) + f'''
Definition sample_text : string := {coq_text(text)}.
Definition sample_leaf := CoqLeaf 12 (-123456789012345678901234567890)%Z sample_text true.
Definition sample_tree := CoqNode sample_leaf sample_leaf.
Definition sample := mkInput 0 123456789012345678901234567890%Z sample_text false
  sample_tree (CoqLeftNext (CoqRightNext CoqStop sample_tree)).
Definition sample_json := encode_input sample.
From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlString.
Extraction "codec.ml" sample_json.
'''
        (run / 'Probe.v').write_text(probe)
        (run / 'driver.ml').write_text('let () = List.iter print_char Codec.sample_json; print_newline ()\n')
        commands = [
            ['bash', str(ROOT / 'environment/env.sh'), 'coqc', '-q', 'Probe.v'],
            ['bash', str(ROOT / 'environment/env.sh'), 'ocamlopt', '-c', 'codec.mli'],
            ['bash', str(ROOT / 'environment/env.sh'), 'ocamlopt', 'codec.ml', 'driver.ml', '-o', 'codec'],
            [str(run / 'codec')],
        ]
        output = None
        for index, command in enumerate(commands):
            result = subprocess.run(command, cwd=run, capture_output=True,
                                    text=True, timeout=120)
            (run / f'{index}.log').write_text(result.stdout + result.stderr)
            self.assertEqual(result.returncode, 0, f'{run}\n{result.stdout}{result.stderr}')
            output = result.stdout
        wire = json.loads(output)
        self.assertEqual(wire, expected)
        self.assertEqual(decode_input(wire, FIELDS, codec.constructor_schema(SCHEMA)), expected)
        bridge = subprocess.run(
            ['bash', str(ROOT / 'environment/env.sh'), 'frontend',
             str(build_bridge()), 'codec',
             str(ROOT / 'scripts/tests/fixtures/property/bridge/basic.watsup')],
            input=json.dumps(list(wire.values())) + '\n', capture_output=True,
            text=True, timeout=90)
        (run / 'bridge.log').write_text(bridge.stdout + bridge.stderr)
        self.assertEqual(bridge.returncode, 0, bridge.stdout + bridge.stderr)
        self.assertEqual(json.loads(bridge.stdout), list(expected.values()))


if __name__ == '__main__':
    unittest.main()
