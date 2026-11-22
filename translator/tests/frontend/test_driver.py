"""Driver safety regressions; no installed frontend is needed."""
import importlib.util
import copy
import hashlib
import json
import tempfile
import pathlib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[3]

class DriverTests(unittest.TestCase):
    def setUp(self):
        spec = importlib.util.spec_from_file_location('translate', ROOT / 'scripts/translate.py')
        self.driver = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.driver)

    def test_hash_mismatch_rejected(self):
        with self.assertRaisesRegex(ValueError, 'SHA-256 mismatch'):
            self.driver.verify_inputs(ROOT, {'inputs': [{'path': 'translator/tests/frontend/test_driver.py', 'sha256': '0' * 64}]})

    def test_escaping_input_rejected(self):
        with self.assertRaisesRegex(ValueError, 'outside worktree'):
            self.driver.verify_inputs(ROOT, {'inputs': [{'path': '/etc/passwd', 'sha256': '0' * 64}]})

    def test_duplicate_input_rejected(self):
        import hashlib
        path = 'translator/tests/frontend/test_driver.py'
        entry = {'path': path, 'sha256': hashlib.sha256((ROOT / path).read_bytes()).hexdigest()}
        with self.assertRaisesRegex(ValueError, 'duplicate input'):
            self.driver.verify_inputs(ROOT, {'inputs': [entry, entry]})

class GenerationPublicationTests(unittest.TestCase):
    """Synthetic files test audit/publication invariants without compiling Coq.

    Every fixture remains beneath ignored evidence; real worktree profiles and
    specification directories are never used as publication destinations.
    """
    def setUp(self):
        spec = importlib.util.spec_from_file_location('translate_safety', ROOT / 'scripts/translate.py')
        self.driver = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.driver)
        base = ROOT / '_opam-testing-theorems/checks'
        base.mkdir(parents=True, exist_ok=True)
        self.workspace = pathlib.Path(tempfile.mkdtemp(prefix='driver-safety.', dir=base))
        self.driver.ROOT = self.workspace
        self.driver.STATE = self.workspace / '_opam-testing-theorems'
        self.source = self.driver.STATE / 'generated'
        (self.source / 'Generated').mkdir(parents=True)
        self.run = self.driver.STATE / 'runs/verification'
        self.run.mkdir(parents=True)
        self.profile_path = self.workspace / 'translator/profiles/p4.json'
        self.profile_path.parent.mkdir(parents=True)
        self.profile_path.write_text(json.dumps({'schema_version': 1, 'name': 'p4'}))
        self.destination = self.workspace / 'specification/p4'
        self.outputs = []
        # Put the initially absent file first: a later conflict must prevent
        # publication of every file, rather than leave a partial update.
        for name, content in [('Generated/Types_0000.v', 'Inductive example := Example.\n'),
                              ('Spec.v', 'Definition example_spec := 0.\n')]:
            (self.source / name).write_text(content)
            self.outputs.append({'path': name, 'sha256': hashlib.sha256(content.encode()).hexdigest()})
        declarations, bindings = [], []
        for i in range(47):
            name = f'builtin_{i:02d}'
            declarations.append({'source_name': name, 'generated_name': 'g_' + name,
                'namespace': 'dec', 'kind': 'BuiltinDecD', 'signature': {}, 'disposition': 'generated-body'})
            bindings.append({'source_name': name, 'profile': 'p4', 'declaration_kind': 'BuiltinDecD',
                'runtime_helper': 'P4.' + name, 'runtime_source': 'Builtins/P4.v', 'native_source': name + '.ml'})
        declarations += [
            {'source_name': 'example', 'generated_name': 'g_type_example', 'namespace': 'type', 'kind': 'TypD', 'signature': None, 'disposition': 'generated-type'},
            {'source_name': 'n', 'generated_name': 'g_var_n', 'namespace': 'var', 'kind': 'VarD', 'signature': None, 'disposition': 'consumed-metadata'}]
        counts = {'generated-type': 1, 'generated-body': 47, 'consumed-metadata': 1, 'pending': 0, 'skipped': 0}
        self.inventory = {'code_generation_complete': True, 'declaration_count': len(declarations),
            'declarations': declarations, 'disposition_counts': counts, 'builtin_bindings': bindings}
        self.manifest = {'status': 'coq-generated', 'code_generation_complete': True, 'coq_compiled': True,
            'disposition_counts': copy.deepcopy(counts), 'builtin_bindings': copy.deepcopy(bindings),
            'output_files': copy.deepcopy(self.outputs)}
        self.write_inventory()

    def write_inventory(self):
        (self.source / 'inventory.json').write_text(json.dumps(self.inventory))

    def test_complete_generation_audit_accepted(self):
        actual = self.driver.verify_generation(self.source, self.manifest, 'p4')
        self.assertEqual(actual['declaration_count'], 49)

    def test_missing_declaration_rejected(self):
        self.inventory['declarations'].pop()
        self.write_inventory()
        with self.assertRaisesRegex(ValueError, 'declaration count'):
            self.driver.verify_generation(self.source, self.manifest, 'p4')

    def test_duplicate_declaration_binding_rejected(self):
        self.inventory['declarations'][1]['generated_name'] = self.inventory['declarations'][0]['generated_name']
        self.write_inventory()
        with self.assertRaisesRegex(ValueError, 'duplicate generated declaration'):
            self.driver.verify_generation(self.source, self.manifest, 'p4')

    def test_unfinished_declaration_rejected(self):
        self.inventory['declarations'][0]['disposition'] = 'indexed-pending-lowering'
        self.write_inventory()
        with self.assertRaisesRegex(ValueError, 'unfinished or incorrect disposition'):
            self.driver.verify_generation(self.source, self.manifest, 'p4')

    def test_missing_builtin_binding_rejected(self):
        self.manifest['builtin_bindings'].pop()
        with self.assertRaisesRegex(ValueError, 'builtin bindings'):
            self.driver.verify_generation(self.source, self.manifest, 'p4')

    def test_duplicate_builtin_binding_rejected(self):
        self.manifest['builtin_bindings'][-1] = copy.deepcopy(self.manifest['builtin_bindings'][0])
        with self.assertRaisesRegex(ValueError, 'builtin bindings'):
            self.driver.verify_generation(self.source, self.manifest, 'p4')

    def test_missing_output_binding_rejected(self):
        self.manifest['output_files'].pop()
        with self.assertRaisesRegex(ValueError, 'exactly cover Coq files'):
            self.driver.verify_generation(self.source, self.manifest, 'p4')

    def test_duplicate_output_binding_rejected(self):
        self.manifest['output_files'].append(copy.deepcopy(self.manifest['output_files'][0]))
        with self.assertRaisesRegex(ValueError, 'duplicate generated output path'):
            self.driver.verify_generation(self.source, self.manifest, 'p4')

    def test_changed_output_rejected(self):
        (self.source / 'Spec.v').write_text('changed after generation\n')
        with self.assertRaisesRegex(ValueError, 'generated output changed'):
            self.driver.verify_generation(self.source, self.manifest, 'p4')

    def test_generated_symlink_rejected(self):
        alias = self.source / 'Generated/Alias.v'
        alias.symlink_to('../Spec.v')
        self.manifest['output_files'].append({'path': 'Generated/Alias.v',
            'sha256': hashlib.sha256((self.source / 'Spec.v').read_bytes()).hexdigest()})
        with self.assertRaisesRegex(ValueError, 'symlink'):
            self.driver.verify_generation(self.source, self.manifest, 'p4')

    def test_publication_requires_successful_coq_compilation(self):
        self.manifest['coq_compiled'] = False
        with self.assertRaisesRegex(ValueError, 'requires complete generation and Coq compilation'):
            self.driver.publish_generated(self.source, 'p4', self.run, self.manifest)
        self.assertFalse(self.destination.exists())

    def test_publication_requires_complete_generation(self):
        self.manifest['code_generation_complete'] = False
        with self.assertRaisesRegex(ValueError, 'requires complete generation and Coq compilation'):
            self.driver.publish_generated(self.source, 'p4', self.run, self.manifest)
        self.assertFalse(self.destination.exists())

    def test_unrelated_conflict_preflight_preserves_all_files(self):
        self.destination.mkdir(parents=True)
        (self.destination / 'Spec.v').write_text('unrelated authored file\n')
        with self.assertRaisesRegex(ValueError, 'unrelated differing file'):
            self.driver.publish_generated(self.source, 'p4', self.run, self.manifest)
        self.assertEqual((self.destination / 'Spec.v').read_text(), 'unrelated authored file\n')
        self.assertFalse((self.destination / 'Generated/Types_0000.v').exists())

    def test_managed_previous_output_archived_before_copy(self):
        self.destination.mkdir(parents=True)
        previous = 'previous verified source\n'
        (self.destination / 'Spec.v').write_text(previous)
        retained = self.destination / 'Generated/Retained.v'
        retained.parent.mkdir()
        retained.write_text('prior managed output retained\n')
        profile = json.loads(self.profile_path.read_text())
        profile['publication'] = {'managed_files': [
            {'path': 'Spec.v', 'sha256': hashlib.sha256(previous.encode()).hexdigest()},
            {'path': 'Generated/Retained.v', 'sha256': hashlib.sha256(retained.read_bytes()).hexdigest()}]}
        registry = self.driver.STATE / 'publication/p4.json'
        registry.parent.mkdir(parents=True)
        registry.write_text(json.dumps(profile['publication']))
        updated = self.driver.publish_generated(self.source, 'p4', self.run, self.manifest)
        self.assertEqual((self.run / 'publication-archive/p4/Spec.v').read_text(), previous)
        self.assertEqual((self.destination / 'Spec.v').read_bytes(), (self.source / 'Spec.v').read_bytes())
        self.assertEqual(retained.read_text(), 'prior managed output retained\n')
        self.assertIn('Generated/Retained.v', self.manifest['publication']['retained_prior_managed_files'])
        self.assertEqual(len(updated['publication']['managed_files']), 3)
        self.assertEqual(json.loads(registry.read_text()), updated['publication'])
        self.assertEqual(json.loads(self.profile_path.read_text()),
                         {'schema_version': 1, 'name': 'p4'})

    def test_run_results_leave_input_profile_unchanged(self):
        before = self.profile_path.read_bytes()
        self.manifest['run'] = str(self.run)
        self.driver.record_results('p4', self.manifest, self.manifest)
        self.assertEqual(self.profile_path.read_bytes(), before)
        result = json.loads((self.run / 'profile-results.json').read_text())
        self.assertEqual(result['validation']['coq_compilation'], 'verified')
        self.assertEqual(len(result['builtin_bindings']), 47)

    def test_checked_publication_records_local_registry(self):
        before = self.profile_path.read_bytes()
        self.driver.publish_generated(self.source, 'p4', self.run, self.manifest)
        registry = self.driver.STATE / 'publication/p4.json'
        self.assertTrue(registry.is_file())
        self.assertEqual(json.loads(registry.read_text())['managed_files'],
                         sorted(self.outputs, key=lambda item: item['path']))
        self.assertEqual(self.profile_path.read_bytes(), before)

    def test_failed_publication_preserves_local_registry(self):
        registry = self.driver.STATE / 'publication/p4.json'
        registry.parent.mkdir(parents=True)
        previous = json.dumps({'managed_files': []})
        registry.write_text(previous)
        self.destination.mkdir(parents=True)
        (self.destination / 'Spec.v').write_text('unrelated authored file\n')
        with self.assertRaisesRegex(ValueError, 'unrelated differing file'):
            self.driver.publish_generated(self.source, 'p4', self.run, self.manifest)
        self.assertEqual(registry.read_text(), previous)
        self.assertFalse((self.destination / 'Generated/Types_0000.v').exists())

    def test_identical_existing_file_is_left_in_place(self):
        self.destination.mkdir(parents=True)
        target = self.destination / 'Spec.v'
        target.write_bytes((self.source / 'Spec.v').read_bytes())
        before = target.stat().st_mtime_ns
        self.driver.publish_generated(self.source, 'p4', self.run, self.manifest)
        self.assertEqual(target.stat().st_mtime_ns, before)
        self.assertEqual(self.manifest['publication']['archived_files'], [])

    def test_publication_rejects_path_traversal(self):
        self.manifest['output_files'][0]['path'] = '../outside.v'
        with self.assertRaisesRegex(ValueError, 'unexpected generated publication path'):
            self.driver.publish_generated(self.source, 'p4', self.run, self.manifest)
        self.assertFalse(self.destination.exists())


if __name__ == '__main__':
    unittest.main()
