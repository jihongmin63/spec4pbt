"""A checked publication binds its source, configuration, and plan artifacts."""
import json
from pathlib import Path
import tempfile
import unittest

from scripts.property import rocq

ROOT = Path(__file__).resolve().parents[2]


class PublicationTests(unittest.TestCase):
    def setUp(self):
        self.directory = Path(tempfile.mkdtemp(prefix='property-publication-',
            dir=ROOT / '_opam-testing-theorems/checks'))
        self.source = self.directory / 'Property.watsup'
        self.source.write_text('var x : nat\nrelation Pre: nat nat hint(input %0)\n'
                               'rule Pre/main: x x\nrelation Goal: nat nat hint(input %0 %1)\n'
                               'rule Goal/main: x x\n')
        self.config = self.directory / 'Property.toml'
        self.config.write_text('precondition="Pre"\ngoal="Goal"\n')

    def test_renderer_rejects_source_config_and_plan_mismatch(self):
        publication = rocq.translate_property(self.source, self.config, self.directory / 'spec')
        for file in (self.source, self.config):
            with self.subTest(file=file.name):
                before = file.read_bytes()
                file.write_bytes(before + b'\n')
                with self.assertRaisesRegex(ValueError, 'changed|mismatch'):
                    rocq.render_original(self.source, self.config, publication=publication)
                file.write_bytes(before)
        evidence = json.loads((publication / 'PassEvidence.json').read_text())
        plan = publication / evidence.get('property_plan', 'PropertyPlan.json')
        plan.write_text(plan.read_text() + '\n')
        with self.assertRaisesRegex(ValueError, 'artifact changed'):
            rocq.render_original(self.source, self.config, publication=publication)

    def test_source_change_between_backend_and_publication_is_rejected(self):
        run, generated = rocq._generate_property(self.source, self.config)
        self.source.write_text(self.source.read_text() + '\n')
        with self.assertRaisesRegex(ValueError, 'source changed'):
            rocq._publish(self.source, self.directory / 'spec', 'fixture', run, generated)
        self.assertFalse((self.directory / 'spec/PassEvidence.json').exists())


if __name__ == '__main__':
    unittest.main()
