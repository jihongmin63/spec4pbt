"""Input wire values retain types and reject extra state or witnesses."""
import unittest
import json
import subprocess

from scripts.property.bridge import ROOT, build_bridge

from scripts.property.codec import CodecError, decode_input, decode_value, encode_value


class CodecTests(unittest.TestCase):
    def test_primitive_and_nested_constructor_roundtrip(self):
        constructors = {'Tree': {'Leaf': ('nat',), 'Node': ('Tree', 'Tree')}}
        wire = {'type': 'Tree', 'constructor': 'Node', 'args': [
            {'type': 'Tree', 'constructor': 'Leaf', 'args': [
                {'type': 'nat', 'value': '3'}]},
            {'type': 'Tree', 'constructor': 'Leaf', 'args': [
                {'type': 'nat', 'value': '8'}]}]}
        value = decode_value(wire, 'Tree', constructors)
        self.assertEqual(encode_value(value), wire)
        self.assertEqual(encode_value(decode_value(
            {'type': 'int', 'value': '-42'}, 'int')),
            {'type': 'int', 'value': '-42'})
        self.assertEqual(encode_value(decode_value(
            {'type': 'text', 'value': 'a'}, 'text')),
            {'type': 'text', 'value': 'a'})

    def test_bad_type_and_extra_input_fields_rejected(self):
        with self.assertRaises(CodecError):
            decode_value({'type': 'nat', 'value': '-1'}, 'nat')
        with self.assertRaises(CodecError):
            decode_value({'type': 'text', 'value': '7'}, 'nat')
        with self.assertRaises(CodecError):
            decode_input({'x': {'type': 'nat', 'value': '7'}, 'fresh_id': 0},
                         ({'name': 'x', 'type': 'nat'},))
        with self.assertRaises(CodecError):
            decode_input({'x': {'type': 'nat', 'value': '7'}, 'b': 10},
                         ({'name': 'x', 'type': 'nat'},))

    def test_non_string_constructor_is_a_codec_error(self):
        for constructor in ([], {}, None, False):
            with self.subTest(constructor=constructor), self.assertRaises(CodecError):
                decode_value({'type': 'Tree', 'constructor': constructor, 'args': []},
                             'Tree', {'Tree': {'Leaf': ()}})

    def test_native_bridge_uses_same_nested_typed_json(self):
        wire = [
            {'type': 'Tree', 'constructor': 'Node', 'args': [
                {'type': 'Tree', 'constructor': 'Leaf', 'args': [
                    {'type': 'nat', 'value': '3'}]},
                {'type': 'Tree', 'constructor': 'Leaf', 'args': [
                    {'type': 'int', 'value': '-2'}]}]},
            {'type': 'text', 'value': 'sample'},
        ]
        process = subprocess.run(
            ['bash', str(ROOT / 'environment/env.sh'), 'frontend',
             str(build_bridge()), 'codec',
             str(ROOT / 'scripts/tests/fixtures/property/bridge/basic.watsup')],
            input=json.dumps(wire) + '\n', capture_output=True, text=True,
            timeout=60)
        self.assertEqual(process.returncode, 0, process.stdout + process.stderr)
        self.assertEqual(json.loads(process.stdout), wire)


if __name__ == '__main__':
    unittest.main()
