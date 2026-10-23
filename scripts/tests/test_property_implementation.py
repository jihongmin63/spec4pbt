"""Implementation manifests are checked before sampling or external execution."""
import json
from pathlib import Path
from types import SimpleNamespace
import tempfile
import unittest

from scripts.property.implementation import load_implementation, validate_snapshot


class ImplementationManifestTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name)
        self.bundle_dir=self.root/'bundle';self.bundle_dir.mkdir()
        (self.bundle_dir/'metadata-config.json').write_text(json.dumps({
            'schema_version':1,'observations':[
                {'id':'copy','relation':'Copy','observe':['%1']},
                {'id':'other','relation':'Other','observe':[]}]}))
        (self.bundle_dir/'catalog-config.json').write_text(
            (self.bundle_dir/'metadata-config.json').read_text())
        (self.bundle_dir/'manifest.json').write_text(json.dumps({'relations':{
            'Copy':{'inputs':[0],'arguments':[{'type':'nat'},{'type':'nat'}]},
            'Other':{'inputs':[0],'arguments':[{'type':'nat'},{'type':'nat'}]},
            'Internal':{'inputs':[0],'arguments':[{'type':'nat'},{'type':'nat'}]}}}))
        (self.bundle_dir/'catalog-manifest.json').write_text(json.dumps({
            'relations': {'Copy': {}, 'Other': {}}}))
        self.bundle=SimpleNamespace(directory=self.bundle_dir,plan={'calls':[{'relation':'Copy','id':'condition.0'}]})
        self.impl=self.root/'implementation.toml'
        (self.root/'run').mkdir()
        (self.root/'run'/'adapter.py').write_text('print(1)\n')
        (self.root/'run'/'target.bin').write_bytes(b'v1')
        self.write('''schema_version = 1
id = "A"
cwd = "run"
[[executions]]
relation = "Copy"
adapter = ["python3", "adapter.py"]
artifacts = ["target.bin"]
''')

    def write(self, text):
        self.impl.write_text(text)

    def test_manifest_relative_cwd_and_dependency_freshness(self):
        binding=load_implementation(self.impl,self.bundle)
        self.assertEqual(binding.cwd,self.root/'run')
        command=binding.for_relation('Copy').adapter
        self.assertTrue(Path(command[0]).is_absolute())
        self.assertEqual(command[1:],['adapter.py'])
        self.assertEqual(validate_snapshot(binding.snapshot,self.bundle)['identity'],binding.identity)
        binding.assert_fresh()
        (self.root/'run'/'target.bin').write_bytes(b'v2')
        with self.assertRaisesRegex(ValueError,'stale'):
            binding.assert_fresh()

    def test_saved_snapshot_validates_without_manifest_or_artifacts(self):
        binding=load_implementation(self.impl,self.bundle)
        snapshot=binding.snapshot
        self.impl.unlink()
        (self.root/'run'/'adapter.py').unlink()
        (self.root/'run'/'target.bin').unlink()
        self.assertEqual(validate_snapshot(snapshot,self.bundle)['identity'],binding.identity)
        snapshot['bindings']['Copy']['adapter'][1]='wrong.py'
        with self.assertRaisesRegex(ValueError,'identity'):
            validate_snapshot(snapshot,self.bundle)

    def test_extensionless_interpreter_script_is_fingerprinted(self):
        script=self.root/'run'/'adapter'
        script.write_text('print(1)\n')
        self.write(self.impl.read_text().replace('"adapter.py"','"adapter"'))
        binding=load_implementation(self.impl,self.bundle)
        script.write_text('print(2)\n')
        with self.assertRaisesRegex(ValueError,'stale'):
            binding.assert_fresh()

    def test_unused_metadata_relation_allowed_but_missing_used_rejected(self):
        binding=load_implementation(self.impl,self.bundle)
        self.assertEqual(set(binding.snapshot['bindings']),{'Copy'})
        self.write('schema_version = 1\nid = "A"\nexecutions = []\n')
        with self.assertRaisesRegex(ValueError,'missing.*Copy'):
            load_implementation(self.impl,self.bundle)

    def test_internal_duplicate_and_unknown_relation_rejected(self):
        original=self.impl.read_text()
        for text,pattern in [
            (original+'\n[[executions]]\nrelation = "Internal"\nadapter = ["python3", "adapter.py"]\n','Internal'),
            (original+'\n[[executions]]\nrelation = "Unknown"\nadapter = ["python3", "adapter.py"]\n','Unknown'),
            (original+'\n[[executions]]\nrelation = "Copy"\nadapter = ["python3", "adapter.py"]\n','duplicate')]:
            self.write(text)
            with self.assertRaisesRegex(ValueError,pattern):
                load_implementation(self.impl,self.bundle)

    def test_empty_observation_still_needs_binding(self):
        self.bundle.plan['calls']=[{'relation':'Other','id':'condition.0'}]
        with self.assertRaisesRegex(ValueError,'missing.*Other'):
            load_implementation(self.impl,self.bundle)

    def test_invalid_fields_types_commands_and_missing_artifact(self):
        original=self.impl.read_text()
        for text,pattern in [
            (original+'surprise = 1\n','field'),
            (original.replace('schema_version = 1','schema_version = true'),'schema'),
            (original.replace('id = "A"','id = ""'),'id'),
            (original.replace('"python3", "adapter.py"',''), 'adapter'),
            (original.replace('"target.bin"','"missing.bin"'),'artifact'),
            (original.replace('"python3", "adapter.py"','"python3", "bad\\u0000.py"'),'NUL')]:
            self.write(text)
            with self.assertRaisesRegex((ValueError,FileNotFoundError),pattern):
                load_implementation(self.impl,self.bundle)


if __name__=='__main__':unittest.main()
