"""Property artifacts stay local without permitting writes into authored sources."""
from pathlib import Path
import tempfile
import unittest

from scripts.property.workflow import _bundle_path


class OutputLayoutTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.project = Path(self.tmp.name).resolve()

    def test_accepts_property_bundle_and_owned_scratch(self):
        for relative in ('properties/progress/bundle', 'build/scratch/Trial/Bundle'):
            with self.subTest(relative=relative):
                self.assertEqual(_bundle_path(relative, self.project), self.project/relative)

    def test_rejects_authored_sources_runs_and_shared_translation_as_bundle(self):
        for relative in ('properties/progress', 'properties/progress/runs',
                         'specifications/p4/translated', 'scripts', 'build',
                         'build/translator', 'out/bundles/progress'):
            with self.subTest(relative=relative):
                with self.assertRaises(ValueError):
                    _bundle_path(relative, self.project)

    def test_rejects_symlinked_property_parent(self):
        properties = self.project/'properties'
        properties.mkdir()
        real = self.project/'real'
        real.mkdir()
        (properties/'alias').symlink_to(real, target_is_directory=True)
        with self.assertRaises(ValueError):
            _bundle_path(properties/'alias/bundle', self.project)
