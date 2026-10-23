"""A property may select only external observations allowed by its spec catalog."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.property.plan import select_external
from scripts.tests import ROOT, ORDERED, SCRATCH


CATALOG = {
    'schema_version': 1,
    'observations': [
        {'id': 'eval', 'relation': 'Eval', 'observe': ['%1']},
        {'id': 'inst', 'relation': 'Inst', 'observe': []},
    ],
}


class ExternalSelectionTests(unittest.TestCase):
    def test_unselected_catalog_relation_is_absent(self):
        chosen = {'schema_version': 1, 'external': [
            {'id': 'inst', 'observe': []},
        ]}
        self.assertEqual(select_external(CATALOG, chosen), {
            'schema_version': 1,
            'observations': [{'id': 'inst', 'relation': 'Inst', 'observe': []}],
        })
        self.assertEqual(CATALOG['observations'][0]['observe'], ['%1'])

    def test_empty_selection_is_internal_only(self):
        self.assertEqual(select_external(CATALOG, {'schema_version': 1, 'external': []}),
                         {'schema_version': 1, 'observations': []})

    def test_selected_output_may_be_narrower_than_catalog(self):
        chosen = {'schema_version': 1, 'external': [
            {'id': 'eval', 'observe': ['%1.VALUE']},
        ]}
        self.assertEqual(select_external(CATALOG, chosen)['observations'][0],
                         {'id': 'eval', 'relation': 'Eval', 'observe': ['%1.VALUE']})

    def test_selected_relation_may_request_status_only(self):
        chosen = {'schema_version': 1, 'external': [
            {'id': 'eval', 'observe': []},
        ]}
        self.assertEqual(select_external(CATALOG, chosen)['observations'][0]['observe'], [])

    def test_unknown_or_duplicate_id_is_rejected(self):
        for entries, message in [
            ([{'id': 'missing', 'observe': []}], 'unknown'),
            ([{'id': 'inst', 'observe': []}, {'id': 'inst', 'observe': []}], 'duplicate'),
        ]:
            with self.subTest(entries=entries), self.assertRaisesRegex(ValueError, message):
                select_external(CATALOG, {'schema_version': 1, 'external': entries})

    def test_wider_and_unrelated_selector_are_rejected(self):
        catalog = copy.deepcopy(CATALOG)
        catalog['observations'][0]['observe'] = ['%1.VALUE']
        for selector in ['%1', '%1.TRACE']:
            with self.subTest(selector=selector), self.assertRaisesRegex(ValueError, 'outside catalog'):
                select_external(catalog, {'schema_version': 1, 'external': [
                    {'id': 'eval', 'observe': [selector]},
                ]})

    def test_overlapping_and_malformed_selection_are_rejected(self):
        for selectors, message in [
            (['%1', '%1.VALUE'], 'overlap'),
            (['%x'], 'selector'),
        ]:
            with self.subTest(selectors=selectors), self.assertRaisesRegex(ValueError, message):
                select_external(CATALOG, {'schema_version': 1, 'external': [
                    {'id': 'eval', 'observe': selectors},
                ]})

    def test_document_shapes_and_catalog_duplicates_are_rejected(self):
        for selection in [
            {'schema_version': 1},
            {'schema_version': True, 'external': []},
            {'schema_version': 1, 'external': [{'id': 'eval'}]},
            {'schema_version': 1, 'external': [], 'observations': []},
        ]:
            with self.subTest(selection=selection), self.assertRaises(ValueError):
                select_external(CATALOG, selection)
        duplicate = copy.deepcopy(CATALOG)
        duplicate['observations'].append({'id': 'eval_again', 'relation': 'Eval', 'observe': []})
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            select_external(duplicate, {'schema_version': 1, 'external': []})

    def test_catalogued_relation_can_be_internal_in_one_property(self):
        from scripts.property.plan import compile_clause
        from scripts.tests.test_property_clause import frontend

        source = 'property probe:\n  (n : nat)\n  true\n  -- Copy: n ~> x\n'
        clause = frontend(source, (ORDERED/'spec.watsup').read_text())
        catalog = {'schema_version': 1, 'observations': [
            {'id': 'copy', 'relation': 'Copy', 'observe': []},
        ]}
        internal = compile_clause(clause, select_external(catalog, {
            'schema_version': 1, 'external': [],
        }))
        external = compile_clause(clause, select_external(catalog, {
            'schema_version': 1, 'external': [{'id': 'copy', 'observe': []}],
        }))
        self.assertEqual(internal['calls'], [])
        self.assertEqual([call['relation'] for call in external['calls']], ['Copy'])


class ExternalSelectionCliTests(unittest.TestCase):
    def test_plan_uses_only_selected_catalog_relations(self):
        with tempfile.TemporaryDirectory(prefix='ExternalPlan', dir=SCRATCH) as tmp:
            root = Path(tmp)
            (root/'observations.toml').write_text('''schema_version = 1
[[observations]]
id = "copy"
relation = "Copy"
observe = ["%1"]
[[observations]]
id = "internal"
relation = "Internal"
observe = ["%1"]
''')
            (root/'external.toml').write_text('''schema_version = 1
[[external]]
id = "copy"
observe = []
''')
            result = subprocess.run([
                sys.executable, '-m', 'scripts.property', 'plan',
                '--spec', str(ORDERED/'spec.watsup'),
                '--property', str(ORDERED/'properties.watsup'),
                '--name', 'progress',
                '--config', str(root/'observations.toml'),
                '--external', str(root/'external.toml'),
            ], cwd=ROOT, capture_output=True, text=True, timeout=60)
            self.assertEqual(result.returncode, 0, result.stderr)
            plan = json.loads(result.stdout)
            self.assertEqual([call['relation'] for call in plan['calls']], ['Copy'])
            self.assertNotIn('Internal', plan['external_relations'])
            self.assertEqual(plan['calls'][0]['profile_selectors'], [])


class ExternalSelectionBuildTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from scripts.property.clause import build_property

        cls.tmp = tempfile.TemporaryDirectory(prefix='ExternalBuild', dir=SCRATCH)
        cls.addClassCleanup(cls.tmp.cleanup)
        cls.root = Path(cls.tmp.name)
        cls.base = 'build.scratch.' + cls.root.name
        cls.catalog = cls.root/'observations.toml'
        cls.catalog.write_text('''schema_version = 1
[[observations]]
id = "copy"
relation = "Copy"
observe = ["%1"]
[[observations]]
id = "internal"
relation = "Internal"
observe = ["%1"]
''')
        cls.selection = cls.root/'external.toml'
        cls.selection.write_text('''schema_version = 1
[[external]]
id = "copy"
observe = ["%1"]
''')
        template = (ORDERED/'templates/copy_positive_proof.lean.in').read_text()
        (cls.root/'Proof.lean').write_text(template.replace('@CONTRACT@', cls.base+'.Bundle.Contract'))
        cls.bundle = build_property(
            project=ROOT, spec_paths=[ORDERED/'spec.watsup'],
            property_path=ORDERED/'properties.watsup', name='positive',
            config_path=cls.catalog, external_path=cls.selection,
            output=cls.root/'Bundle', proof_module=cls.base+'.Proof',
            property_proof='ClauseCopy.property_correct', timeout_seconds=120)

    def test_bundle_freezes_only_selected_observations(self):
        metadata = json.loads((self.bundle.directory/'metadata-config.json').read_text())
        self.assertEqual(metadata, {'schema_version': 1, 'observations': [
            {'id': 'copy', 'relation': 'Copy', 'observe': ['%1']},
        ]})
        self.assertEqual([call['relation'] for call in self.bundle.plan['calls']], ['Copy'])

    def test_changing_either_authored_file_stales_bundle(self):
        for path in [self.catalog, self.selection]:
            original = path.read_text()
            try:
                path.write_text(original + '\n# edited\n')
                with self.subTest(path=path), self.assertRaisesRegex(ValueError, 'stale'):
                    self.bundle.assert_fresh()
            finally:
                path.write_text(original)
        self.bundle.assert_fresh()

    def test_shared_implementation_may_bind_unselected_catalog_relation(self):
        from scripts.property.implementation import load_implementation, validate_snapshot

        manifest = self.root/'shared-implementation.toml'
        manifest.write_text(f'''schema_version = 1
id = "shared"
cwd = "{ROOT}"
[[executions]]
relation = "Copy"
adapter = ["python3", "{ORDERED/'adapter.py'}"]
[[executions]]
relation = "Internal"
adapter = ["python3", "{ORDERED/'adapter.py'}"]
''')
        implementation = load_implementation(manifest, self.bundle)
        self.assertEqual(set(implementation.snapshot['bindings']), {'Copy', 'Internal'})
        self.assertEqual(validate_snapshot(implementation.snapshot, self.bundle)['identity'],
                         implementation.identity)

    def test_build_rejects_invalid_unselected_catalog_relation(self):
        from scripts.property.clause import build_property

        invalid = self.root/'invalid-observations.toml'
        invalid.write_text(self.catalog.read_text() + '''
[[observations]]
id = "missing"
relation = "Missing"
observe = []
''')
        template = (ORDERED/'templates/copy_positive_proof.lean.in').read_text()
        (self.root/'InvalidProof.lean').write_text(
            template.replace('@CONTRACT@', self.base+'.InvalidBundle.Contract'))
        with self.assertRaisesRegex((ValueError, ChildProcessError), 'Missing|unknown observation'):
            build_property(
                project=ROOT, spec_paths=[ORDERED/'spec.watsup'],
                property_path=ORDERED/'properties.watsup', name='positive',
                config_path=invalid, external_path=self.selection,
                output=self.root/'InvalidBundle', proof_module=self.base+'.InvalidProof',
                property_proof='ClauseCopy.property_correct', timeout_seconds=120)


if __name__ == '__main__':
    unittest.main()
