"""The generator returns only typed Input fields and preserves None."""
import unittest

from scripts.property.generation import GenerationError, load_samples


class GenerationTests(unittest.TestCase):
    def test_samples_preserve_none_and_validate_input(self):
        # A small local list exercises the codec without rerunning extraction.
        data = [None, {'x': {'type': 'nat', 'value': '7'}}]
        result = load_samples(data, ({'name': 'x', 'type': 'nat'},))
        self.assertIsNone(result[0])
        self.assertEqual(result[1]['x']['value'], '7')

    def test_generated_witness_or_state_is_rejected(self):
        with self.assertRaises(GenerationError):
            load_samples([{'x': {'type': 'nat', 'value': '7'}, 'witness': 10}],
                         ({'name': 'x', 'type': 'nat'},))


if __name__ == '__main__':
    unittest.main()
