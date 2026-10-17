"""The direct pipeline preserves donor bytes and publishes complete checked bundles."""
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from p4bridge.translate import generate, _publish, source_identity
from p4bridge.toolchain import UPSTREAM, pinned_revision, resolve_toolchain

ROOT = Path(__file__).resolve().parents[2]


class TranslationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.project = Path(self.temp.name)
        shutil.copyfile(ROOT / 'lean-toolchain', self.project / 'lean-toolchain')
        (self.project / 'lakefile.toml').write_text('name = "direct_test"\nversion = "0.1.0"\n')
        self.output = self.project / 'Generated'
        self.source = ROOT / 'specifications/p4record/spec.watsup'
        self.config = ROOT / 'specifications/p4record/observations.toml'

    def test_bundle_keeps_exact_noncomputable_donor_output_and_metadata_roles(self):
        generate(self.project, self.output, self.config, [self.source])
        tool = resolve_toolchain(ROOT)
        expected = subprocess.check_output([str(tool.executable), str(self.source)])
        self.assertEqual((self.output / 'Spec.lean').read_bytes(), expected)
        manifest = json.loads((self.output / 'manifest.json').read_text())
        self.assertEqual(manifest['relations']['Eval']['inputs'], [0])
        self.assertEqual(set(p.name for p in self.output.iterdir()),
            {'Spec.lean', 'Transport.lean', 'manifest.json', 'translation.json', 'observations.toml'})
        provenance = json.loads((self.output / 'translation.json').read_text())
        self.assertEqual(provenance['mode'], 'ordered')
        self.assertEqual(provenance['spec_module'], 'Generated.Spec')
        self.assertEqual(provenance['transport_module'], 'Generated.Transport')
        self.assertEqual(provenance['p4_spectec'],
                         {'url': UPSTREAM, 'revision': pinned_revision(ROOT)})
        self.assertEqual(provenance['toolchain']['revision'], tool.revision)
        self.assertNotEqual(provenance['p4_spectec']['revision'], tool.revision)

    def test_executable_opt_in_passes_real_donor_flag(self):
        generate(self.project, self.output, self.config, [self.source], executable=True)
        tool = resolve_toolchain(ROOT)
        expected = subprocess.check_output([str(tool.executable), '--executable', str(self.source)])
        self.assertEqual((self.output / 'Spec.lean').read_bytes(), expected)

    def test_existing_destination_is_preserved(self):
        self.output.mkdir()
        marker = self.output / 'keep'
        marker.write_text('original')
        with self.assertRaises(FileExistsError):
            generate(self.project, self.output, self.config, [self.source])
        self.assertEqual(marker.read_text(), 'original')

    def test_invalid_input_selection_publishes_nothing(self):
        config = self.project / 'invalid.toml'
        config.write_text('schema_version = 1\n[[observations]]\nid="x"\nrelation="Eval"\nobserve=["%0"]\n')
        with self.assertRaisesRegex(ValueError, 'input'):
            generate(self.project, self.output, config, [self.source])
        self.assertFalse(self.output.exists())

    def test_source_failure_publishes_nothing(self):
        source = self.project / 'invalid.watsup'
        source.write_text('definitely not a specification\n')
        with self.assertRaises(ValueError):
            generate(self.project, self.output, self.config, [source])
        self.assertFalse(self.output.exists())

    def test_destination_outside_project_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'within|inside'):
            generate(self.project, self.project.parent / 'outside', self.config, [self.source])

    def test_racing_empty_destination_is_never_replaced(self):
        stage = self.project / 'stage'
        stage.mkdir()
        (stage / 'Spec.lean').write_text('checked artifact')
        self.output.mkdir()
        with self.assertRaises(FileExistsError):
            _publish(stage, self.output)
        self.assertEqual(list(self.output.iterdir()), [])
        self.assertEqual((stage / 'Spec.lean').read_text(), 'checked artifact')

    def test_bad_external_model_never_publishes_a_bundle(self):
        fixture = ROOT / 'p4bridge/tests/fixtures/extern.watsup'
        config = self.project / 'extern.toml'
        config.write_text('schema_version = 1\n[[observations]]\nid="value"\nrelation="Copy"\nobserve=["%1"]\n')
        model = self.project / 'invalid-model.lean'
        model.write_text('def broken := definitelyMissingName\n')
        with self.assertRaisesRegex(ValueError, 'definitelyMissingName'):
            generate(self.project, self.output, config, [fixture], transport_model=model)
        self.assertFalse(self.output.exists())

    def test_explicit_external_model_is_used_and_fingerprinted(self):
        fixture = ROOT / 'p4bridge/tests/fixtures/extern.watsup'
        config = self.project / 'extern.toml'
        config.write_text('schema_version = 1\n[[observations]]\nid="value"\nrelation="Copy"\nobserve=["%1"]\n')
        model = ROOT / 'p4bridge/tests/fixtures/external-nat-model.lean'
        generate(self.project, self.output, config, [fixture], transport_model=model)
        provenance = json.loads((self.output / 'translation.json').read_text())
        self.assertEqual(provenance['transport_model']['path'], str(model))
        self.assertEqual(len(provenance['transport_model']['sha256']), 64)

    def test_directory_provenance_includes_linked_sources_and_skips_include(self):
        sources = self.project / 'sources'
        actual = self.project / 'actual'
        sources.mkdir()
        actual.mkdir()
        (sources / 'anchor.watsup').write_text('')
        shutil.copyfile(self.source, actual / 'spec.watsup')
        (sources / 'linked').symlink_to(actual, target_is_directory=True)
        (sources / 'include').mkdir()
        (sources / 'include/ignored.watsup').write_text('not a specification')
        generate(self.project, self.output, self.config, [sources])
        provenance = json.loads((self.output / 'translation.json').read_text())
        self.assertEqual(set(provenance['sources']),
                         {str(sources / 'anchor.watsup'), str(sources / 'linked/spec.watsup')})
        before = source_identity([sources])
        (actual / 'spec.watsup').write_text('changed semantics')
        self.assertNotEqual(source_identity([sources]), before)

    def test_directory_cycle_is_rejected_before_donor_recursion(self):
        sources = self.project / 'sources'
        sources.mkdir()
        (sources / 'loop').symlink_to(sources, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, 'cycle'):
            source_identity([sources])


if __name__ == '__main__':
    unittest.main()
