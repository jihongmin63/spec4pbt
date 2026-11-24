"""Shared manifests resolve independent of properties and working directories."""
from dataclasses import FrozenInstanceError
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from scripts.property.bridge import ROOT
from scripts.property.model import CompileError
try:
    from scripts.property.setup import load_implementation, load_specification
except ImportError:
    load_implementation = load_specification = None


class SetupTests(unittest.TestCase):
    def setUp(self):
        parent = ROOT / '_opam-testing-theorems/checks'
        parent.mkdir(parents=True, exist_ok=True)
        self.temporary = tempfile.TemporaryDirectory(dir=parent, prefix='shared-setup-')
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        (self.root / 'source').mkdir()
        (self.root / 'source/Spec.watsup').write_text('relation B: nat nat\n')
        (self.root / 'source/Extra.watsup').write_text('var x : nat\n')
        self.spec_manifest = self.root / 'Specification.toml'
        self.spec_manifest.write_text('id="demo"\nsources=["source/Spec.watsup"]\nprofile="fixture"\n')
        (self.root / 'demo_external.py').write_text('print("demo")\n')
        (self.root / 'helper.py').write_text('value = 4\n')
        self.adapter_manifest = self.root / 'Adapter.toml'
        self.adapter_text = ('specification="demo"\ndependencies=["helper.py"]\n'
                             '[[external]]\nrelation="External"\nadapter="demo"\n'
                             'command=["python3", "demo_external.py"]\n'
                             'conversion="json-v1"\nobserved_outputs=[0]\n')
        self.adapter_manifest.write_text(self.adapter_text)

    def require_loaders(self):
        self.assertTrue(callable(load_specification), 'shared setup loaders must exist')

    def assert_invalid(self, loader, manifest, text, code, *args):
        manifest.write_text(text)
        with self.assertRaises(CompileError) as caught:
            loader(manifest, *args)
        self.assertEqual(caught.exception.code, code)
        self.assertIsInstance(caught.exception.details, dict)
        self.assertIn(str(manifest), str(caught.exception))

    def test_ordered_sources_and_namespace_have_semantic_file_identities(self):
        self.require_loaders()
        self.spec_manifest.write_text('id="demo"\nsources=["source/Extra.watsup", "source/Spec.watsup"]\nprofile="fixture"\n')
        spec = load_specification(self.spec_manifest)
        self.assertEqual(spec.id, 'demo')
        self.assertEqual(spec.namespace, 'FixtureSpec')
        self.assertEqual(spec.sources, (self.root / 'source/Extra.watsup', self.root / 'source/Spec.watsup'))
        self.assertEqual(set(spec.hashes), {str(self.spec_manifest), *(str(p) for p in spec.sources)})
        self.assertEqual(spec.hashes[str(spec.sources[0])], hashlib.sha256(b'var x : nat\n').hexdigest())
        self.assertEqual(load_specification(self.root), spec)
        with self.assertRaises(FrozenInstanceError):
            spec.id = 'changed'
        with self.assertRaises(TypeError):
            spec.hashes['changed'] = 'bad'

    def test_implementation_reuses_setup_and_resolves_and_hashes_code_dependencies(self):
        self.require_loaders()
        spec = load_specification(self.spec_manifest)
        setup = load_implementation(self.adapter_manifest, spec)
        self.assertEqual(setup.specification, 'demo')
        self.assertEqual(setup.commands, {'demo': ['python3', str(self.root / 'demo_external.py')]})
        self.assertEqual(setup.external, ({'relation': 'External', 'adapter': 'demo',
                                          'conversion': 'json-v1', 'observed_outputs': [0]},))
        self.assertEqual(set(setup.hashes), {str(self.adapter_manifest), str(self.root / 'demo_external.py'), str(self.root / 'helper.py')})
        self.assertEqual(load_implementation(self.root, spec), setup)
        with self.assertRaises(TypeError):
            setup.commands['demo'].append('oops')
        with self.assertRaises(TypeError):
            setup.external[0]['observed_outputs'].append(1)
        with self.assertRaises(TypeError):
            setup.commands.clear()
        (self.root / 'helper.py').write_text('value = 5\n')
        self.assertNotEqual(load_implementation(self.adapter_manifest, spec).hashes, setup.hashes)

    def test_profile_namespace_must_match_translator(self):
        self.require_loaders()
        for profile, namespace in [('p4', 'P4Spec'), ('wasm', 'WasmSpec'), ('fixture', 'FixtureSpec')]:
            self.spec_manifest.write_text(f'id="demo"\nsources=["source/Spec.watsup"]\nprofile="{profile}"\n')
            self.assertEqual(load_specification(self.spec_manifest).namespace, namespace)
        self.assert_invalid(load_specification, self.spec_manifest,
                            'id="demo"\nsources=["source/Spec.watsup"]\nprofile="p4"\nnamespace="FixtureSpec"\n', 'invalid_namespace')

    def test_specification_rejects_invalid_selection_and_sources(self):
        self.require_loaders()
        cases = [
            ('sources=["source/Spec.watsup"]\nprofile="fixture"\n', 'invalid_identifier'),
            ('id=" "\nsources=["source/Spec.watsup"]\nprofile="fixture"\n', 'invalid_identifier'),
            ('id="demo"\nsources=[]\nprofile="fixture"\n', 'invalid_sources'),
            ('id="demo"\nsources="source/Spec.watsup"\nprofile="fixture"\n', 'invalid_sources'),
            ('id="demo"\nsources=["source/Spec.watsup", "source/../source/Spec.watsup"]\nprofile="fixture"\n', 'duplicate_source'),
            ('id="demo"\nsources=["missing.watsup"]\nprofile="fixture"\n', 'missing_file'),
            ('id="demo"\nsources=["source/Spec.watsup"]\nprofile="typo"\n', 'invalid_profile'),
            ('id="demo"\nsources=["source/Spec.watsup"]\nprofile="fixture"\ngoal="Goal"\n', 'unknown_field'),
            ('id="demo"\nsources=["source/Spec.watsup"]\nprofile="fixture"\nnamepsace="FixtureSpec"\n', 'unknown_field'),
        ]
        for text, code in cases:
            with self.subTest(code=code, text=text):
                self.assert_invalid(load_specification, self.spec_manifest, text, code)

    def test_external_catalog_validates_schema_before_relation_typing(self):
        self.require_loaders()
        spec = load_specification(self.spec_manifest)
        cases = [
            (self.adapter_text.replace('specification="demo"', 'specification="other"'), 'specification_mismatch'),
            (self.adapter_text.replace('command=["python3", "demo_external.py"]', 'command="python3 demo_external.py"'), 'invalid_command'),
            (self.adapter_text.replace('observed_outputs=[0]', 'observed_outputs=[true]'), 'invalid_observed_outputs'),
            (self.adapter_text.replace('observed_outputs=[0]', 'observed_outputs=[-1]'), 'invalid_observed_outputs'),
            (self.adapter_text.replace('observed_outputs=[0]', 'observed_outputs=[0,0]'), 'invalid_observed_outputs'),
            (self.adapter_text.replace('conversion="json-v1"', 'conversion="json-v2"'), 'invalid_conversion'),
            (self.adapter_text.replace('demo_external.py', 'missing.py'), 'missing_file'),
            (self.adapter_text.replace('helper.py', 'missing.py'), 'missing_file'),
            (self.adapter_text + 'observed_output=[0]\n', 'unknown_field'),
            (self.adapter_text + self.adapter_text[self.adapter_text.index('[[external]]'):], 'duplicate_relation'),
        ]
        for text, code in cases:
            with self.subTest(code=code, text=text):
                self.assert_invalid(load_implementation, self.adapter_manifest, text, code, spec)
        self.adapter_manifest.write_text(self.adapter_text.replace('observed_outputs=[0]', 'observed_outputs=[6,2]'))
        self.assertEqual(load_implementation(self.adapter_manifest, spec).external[0]['observed_outputs'], [2,6])

    def test_command_preserves_literal_arguments_including_empty_strings(self):
        spec = load_specification(self.spec_manifest)
        cases = [
            ['python3', 'demo_external.py', 'https://localhost/endpoint', '1/2',
             r'a/b\w+', '{"path":"remote/file.py"}', 'missing.py', ''],
            ['python3', '-c', 'print("https://localhost/endpoint")', ''],
            ['python3', '-m', 'some.module', 'https://localhost/endpoint', ''],
        ]
        for command in cases:
            with self.subTest(command=command):
                self.adapter_manifest.write_text(self.adapter_text.replace(
                    'command=["python3", "demo_external.py"]', 'command=' + json.dumps(command)))
                setup = load_implementation(self.adapter_manifest, spec)
                expected = command.copy()
                if expected[1] == 'demo_external.py':
                    expected[1] = str(self.root / 'demo_external.py')
                self.assertEqual(setup.commands['demo'], expected)

    def test_python_control_operands_preserve_literals_when_matching_local_files(self):
        spec = load_specification(self.spec_manifest)
        for name in ('pass', 'demo.module', 'ignore', 'utf8'):
            (self.root / name).write_text('local dependency\n')
        commands = [
            ['python3', '-c', 'pass', ''],
            ['python3', '-m', 'demo.module', ''],
            ['python3', '-W', 'ignore', '-X', 'utf8', 'demo_external.py'],
        ]
        for command in commands:
            with self.subTest(command=command):
                self.adapter_manifest.write_text(self.adapter_text.replace(
                    'command=["python3", "demo_external.py"]', 'command=' + json.dumps(command)))
                setup = load_implementation(self.adapter_manifest, spec)
                expected = command.copy()
                if expected[-1] == 'demo_external.py':
                    expected[-1] = str(self.root / 'demo_external.py')
                self.assertEqual(setup.commands['demo'], expected)
                self.assertTrue(all(str(self.root / name) not in setup.hashes
                                    for name in ('pass', 'demo.module', 'ignore', 'utf8')))

    def test_command_resolves_python_script_without_extension_and_explicit_file_arguments(self):
        spec = load_specification(self.spec_manifest)
        (self.root / 'worker').write_text('pass\n')
        command = ['python3', '-u', 'worker', './helper.py', 'source/Spec.watsup']
        self.adapter_manifest.write_text(self.adapter_text.replace(
            'command=["python3", "demo_external.py"]', 'command=' + json.dumps(command)))
        setup = load_implementation(self.adapter_manifest, spec)
        self.assertEqual(setup.commands['demo'], ['python3', '-u', str(self.root / 'worker'),
                                               str(self.root / 'helper.py'), str(self.root / 'source/Spec.watsup')])
        self.assertIn(str(self.root / 'worker'), setup.hashes)
        self.assertIn(str(self.root / 'source/Spec.watsup'), setup.hashes)
        for command in [['python3', '-u', 'missing'], ['python3', 'demo_external.py', './missing'], ['', 'demo_external.py']]:
            with self.subTest(command=command):
                code = 'invalid_command' if not command[0] else 'missing_file'
                self.assert_invalid(load_implementation, self.adapter_manifest, self.adapter_text.replace(
                    'command=["python3", "demo_external.py"]', 'command=' + json.dumps(command)), code, spec)

    def test_adapter_name_can_be_shared_but_conflicting_commands_are_rejected(self):
        self.require_loaders()
        spec = load_specification(self.spec_manifest)
        second = self.adapter_text[self.adapter_text.index('[[external]]'):].replace('relation="External"', 'relation="Nested"')
        self.adapter_manifest.write_text(self.adapter_text + second)
        self.assertEqual(len(load_implementation(self.adapter_manifest, spec).external), 2)
        (self.root / 'other.py').write_text('pass\n')
        self.assert_invalid(load_implementation, self.adapter_manifest,
                            self.adapter_text + second.replace('demo_external.py', 'other.py'), 'conflicting_command', spec)

    def test_paths_outside_worktree_are_rejected_even_through_symlinks(self):
        self.require_loaders()
        with tempfile.TemporaryDirectory() as outside:
            external = Path(outside) / 'Spec.watsup'
            external.write_text('var x : nat\n')
            (self.root / 'escape.watsup').symlink_to(external)
            self.assert_invalid(load_specification, self.spec_manifest,
                                'id="demo"\nsources=["escape.watsup"]\nprofile="fixture"\n', 'path_outside_worktree')
            with self.assertRaises(CompileError) as caught:
                load_specification(external)
            self.assertEqual(caught.exception.code, 'path_outside_worktree')
        self.spec_manifest.write_text('id="demo"\nsources=["source/Spec.watsup"]\nprofile="fixture"\n')
        self.assert_invalid(load_implementation, self.adapter_manifest,
                            self.adapter_text.replace('helper.py', '/etc/passwd'), 'path_outside_worktree', load_specification(self.spec_manifest))

    def test_invalid_source_path_is_reported_as_compile_error(self):
        self.assert_invalid(load_specification, self.spec_manifest,
                            'id="demo"\nsources=["bad\\u0000.watsup"]\nprofile="fixture"\n',
                            'invalid_path')

    def test_bad_toml_is_reported_as_compile_error(self):
        self.require_loaders()
        self.assert_invalid(load_specification, self.spec_manifest, 'id = [', 'invalid_manifest')


if __name__ == '__main__':
    unittest.main()
