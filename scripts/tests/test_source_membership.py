"""A loaded certificate must notice new files in a selected spec directory."""
from pathlib import Path
import tempfile
import unittest

from scripts.property.clause import CertifiedProperty
from scripts.toolchain import resolve_toolchain, source_identity
from scripts.tests import ROOT, SCRATCH


class SourceMembershipTests(unittest.TestCase):
    def test_added_spec_file_invalidates_loaded_bundle(self):
        with tempfile.TemporaryDirectory(prefix='SourceMembership', dir=SCRATCH) as tmp:
            directory = Path(tmp)
            spec = directory/'spec'
            spec.mkdir()
            (spec/'original.watsup').write_text('syntax n = nat\n')
            tool = resolve_toolchain(ROOT)
            bundle = CertifiedProperty(ROOT,directory,{},'Test','Test',tool.executable,
                (spec,),directory/'property.watsup','test',tool.identity(),source_identity([spec]))
            bundle.assert_fresh()
            (spec/'added.watsup').write_text('syntax other = nat\n')
            with self.assertRaisesRegex(ValueError, 'stale|source selection'):
                bundle.assert_fresh()
