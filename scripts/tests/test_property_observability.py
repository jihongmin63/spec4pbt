"""Compile-time K propagation over typed AL relation calls."""
from pathlib import Path
import tempfile
import unittest

from scripts.property.compiler import CompileError, analyze_replay, compile_spec, frontend_check


ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / 'scripts/tests/fixtures/property/bridge'
ANALYSIS_FIXTURE = ROOT / 'scripts/tests/fixtures/property/observability'


class ObservabilityTests(unittest.TestCase):
    def test_scope_metadata_marks_direct_constructs_without_following_helpers(self):
        report = frontend_check(ANALYSIS_FIXTURE / 'scope.watsup')
        definitions = {item['name']: item for item in report['definitions']}
        for relation, kind in (('Iteration', 'iteration'), ('HigherOrder', 'higher_order')):
            with self.subTest(relation=relation):
                items = definitions[relation].get('unsupported_constructs', [])
                self.assertIn(kind, [item['kind'] for item in items])
                self.assertTrue(all('scope.watsup' in item['source'] for item in items))
        self.assertEqual(definitions['Pre']['unsupported_constructs'], [])
        self.assertEqual(definitions['Goal']['unsupported_constructs'], [])
        self.assertEqual(definitions['Negation']['unsupported_constructs'], [])
        self.assertEqual(definitions['Fallback']['unsupported_constructs'], [])

    def analysis_model(self, fixture, pre='Pre', external=None, replacements=()):
        directory = tempfile.TemporaryDirectory(dir=ROOT / '_opam-testing-theorems')
        self.addCleanup(directory.cleanup)
        directory = Path(directory.name)
        source = directory / fixture
        contents = (ANALYSIS_FIXTURE / fixture).read_text()
        for before, after in replacements:
            self.assertIn(before, contents)
            contents = contents.replace(before, after)
        source.write_text(contents)
        settings = f'precondition = "{pre}"\ngoal = "Goal"\n'
        for relation, positions in (external or {}).items():
            settings += (f'\n[[external]]\nrelation = "{relation}"\n'
                         'adapter = "not_executed"\nconversion = "json-v1"\n'
                         f'observed_outputs = {list(positions)}\n')
        config = directory / 'Property.toml'
        config.write_text(settings)
        return compile_spec(source, config)

    def model(self, source='partial.watsup', first=(0,), whole_helper=False):
        text = (FIXTURE / 'Property.toml').read_text()
        text = text.replace('observed_outputs = [0]',
                            'observed_outputs = [' + ', '.join(map(str, first)) + ']', 1)
        if whole_helper:
            text += ('\n[[external]]\nrelation = "H"\n'
                     'adapter = "whole_helper"\nconversion = "json-v1"\n'
                     'observed_outputs = [0]\n')
        directory = tempfile.TemporaryDirectory(dir=ROOT / '_opam-testing-theorems')
        self.addCleanup(directory.cleanup)
        config = Path(directory.name) / 'Property.toml'
        config.write_text(text)
        return compile_spec(FIXTURE / source, config)

    def test_unused_unobserved_slot_is_allowed(self):
        report = analyze_replay(self.model())
        self.assertIn(0, report['guaranteed_outputs']['Pre'])
        self.assertEqual(report['projection']['E1'], [0])
        self.assertEqual(len(report['al_md5']), 32)
        calls = [item for item in report['premises'] if item['relation'] == 'Pre']
        self.assertEqual([item['kind'] for item in calls], ['E1', 'E2'])
        self.assertIn('x', calls[0]['known_before'])
        self.assertIn('y', calls[0]['introduced'])
        self.assertNotIn('u', calls[0]['known_after'])
        self.assertIn('y', calls[1]['required'])
        self.assertIn('partial.watsup', calls[1]['source'])

    def test_missing_y_reports_producer_and_consumer(self):
        with self.assertRaises(CompileError) as caught:
            analyze_replay(self.model(first=()))
        diagnostic = str(caught.exception)
        self.assertIn('y', diagnostic)
        self.assertIn('E1', diagnostic)
        self.assertIn('E2', diagnostic)
        self.assertIn('consumer E2 input slot 0', diagnostic)
        self.assertIn('partial.watsup', diagnostic)
        premise = caught.exception.details['premise']
        self.assertEqual(premise['inputs'][0]['input_position'], 0)
        self.assertEqual(premise['inputs'][0]['variables'], ['y'])

    def test_used_unobserved_u_is_rejected(self):
        with self.assertRaises(CompileError) as caught:
            analyze_replay(self.model(source='partial_used_u.watsup'))
        self.assertIn('u', str(caught.exception))

    def test_helper_classification_does_not_hide_nested_obligation(self):
        report = analyze_replay(self.model(source='helper.watsup'))
        self.assertTrue(report['external_classification']['H'])
        self.assertEqual(report['guaranteed_outputs']['H'], [0])
        with self.assertRaises(CompileError) as caught:
            analyze_replay(self.model(source='helper.watsup', first=()))
        self.assertIn('consumer E2', str(caught.exception))

    def test_nested_whole_helper_adapter_is_rejected(self):
        with self.assertRaises(CompileError) as caught:
            analyze_replay(self.model(source='helper.watsup', whole_helper=True))
        self.assertIn('nested boundary', str(caught.exception))

    def test_multiple_rules_intersect_guaranteed_outputs(self):
        with self.assertRaises(CompileError) as caught:
            analyze_replay(self.model(source='multi_rule.watsup'))
        self.assertIn('Pre public output slot 0 unavailable', str(caught.exception))

    def test_classification_stops_at_explicit_boundary_specification(self):
        model = self.analysis_model('graphs.watsup', pre='PreBoundary', external={'E': [0]})
        report = analyze_replay(model)
        self.assertTrue(report['external_classification']['H'])
        self.assertFalse(report['external_classification']['I'])
        self.assertEqual(report['classification_reasons']['H']['kind'], 'external_only_helper')
        self.assertEqual(report['classification_reasons']['H']['boundaries'], ['E'])
        self.assertEqual(report['classification_reasons']['H']['internal_calls'], [])
        self.assertEqual(report['classification_reasons']['E']['kind'], 'explicit_boundary')

    def test_pure_and_external_recursive_components_have_distinct_contracts(self):
        for pre, relation, expected in (
                ('PrePure', 'PureA', False), ('PreExternal', 'ExternalA', True)):
            with self.subTest(pre=pre):
                report = analyze_replay(self.analysis_model('graphs.watsup', pre=pre,
                                                            external={'E': [0]}))
                self.assertEqual(report['external_classification'][relation], expected)
                self.assertEqual(report['guaranteed_outputs'][relation], [0])
        with self.assertRaises(CompileError) as caught:
            analyze_replay(self.analysis_model('graphs.watsup', pre='PreCycle',
                                              external={'E': [0]}))
        self.assertIn('PreCycle public output slot 0 unavailable', str(caught.exception))
        self.assertIn('CycleA', str(caught.exception))
        self.assertIn('graphs.watsup', str(caught.exception))

    def test_mixed_helper_and_fresh_classification(self):
        report = analyze_replay(self.analysis_model('graphs.watsup', pre='PreMixed',
                                                    external={'E': [0]}))
        self.assertFalse(report['external_classification']['Mixed'])
        self.assertEqual(report['classification_reasons']['Mixed']['internal_calls'], ['I'])
        self.assertTrue(report['external_classification']['FreshHelper'])
        self.assertFalse(report['external_classification']['PureFresh'])

    def test_nested_missing_observation_keeps_helper_path_and_known_variables(self):
        with self.assertRaises(CompileError) as caught:
            analyze_replay(self.analysis_model('graphs.watsup', pre='PreOuter',
                                              external={'E': []}))
        message = str(caught.exception)
        self.assertIn('PreOuter -> Outer -> Mixed', message)
        self.assertIn('producer E output slot 0', message)
        self.assertIn('consumer I', message)
        self.assertIn('known before: x', message)
        evidence = getattr(caught.exception, 'details', None)
        self.assertIsInstance(evidence, dict)
        self.assertEqual(evidence['helper_path'], ['PreOuter', 'Outer', 'Mixed'])
        self.assertEqual(evidence['premise']['kind'], 'I')
        self.assertEqual(evidence['premise']['known_before'], ['x'])
        self.assertEqual(evidence['guaranteed_outputs']['E'], [])
        self.assertEqual(evidence['classification_reasons']['E']['kind'], 'explicit_boundary')
        self.assertTrue(any(item['relation'] == 'Mixed' and item['kind'] == 'E'
                            for item in evidence['premises']))
        self.assertEqual(len(evidence['spec_al_md5']), 32)

    def test_repeated_bound_constant_and_constructor_outputs_require_observation(self):
        uses = (
            ('  -- Pair: x y u', '  -- Pair: x y y'),
            ('  -- Pair: x y u', '  -- Pair: x y x'),
            ('  -- Pair: x y u', '  -- Pair: x y 7'),
            ('  -- Tagged: x c', '  -- Tagged: x RED'),
            ('  -- if z = y', '  -- if z = u'),
            ('  -- if z = y', '  -- if u = 7\n  -- if z = y'),
            ('  -- if z = y', '  -- I: u z'),
        )
        for before, after in uses:
            with self.subTest(use=after):
                model = self.analysis_model('output_uses.watsup',
                    external={'Pair': [0], 'Tagged': []}, replacements=[(before, after)])
                with self.assertRaises(CompileError) as caught:
                    analyze_replay(model)
                self.assertIn('output_uses.watsup', str(caught.exception))

    def test_manifest_maps_original_slots_to_projected_slots(self):
        report = analyze_replay(self.analysis_model('output_uses.watsup',
            external={'Pair': [1], 'Tagged': []},
            replacements=[('  -- if z = y', '  -- if z = u')]))
        self.assertEqual(report['projection']['Pair'], [1])
        manifest = report['projection_manifest']['Pair']
        self.assertEqual([(slot['original_position'], slot['projected_position'], slot['type'])
                          for slot in manifest], [(0, None, 'nat'), (1, 0, 'nat')])
        self.assertTrue(all('output_uses.watsup' in slot['source'] for slot in manifest))

    def test_nested_boundary_rejection_still_checks_replaced_specification(self):
        with self.assertRaises(CompileError) as caught:
            analyze_replay(self.analysis_model('graphs.watsup', pre='PreBoundary',
                                              external={'E': [0], 'I': [0]}))
        self.assertIn('nested boundary I', str(caught.exception))

    def test_explicit_boundary_does_not_project_replaced_specification_body(self):
        report = analyze_replay(self.analysis_model('output_uses.watsup',
            external={'Pair': [0], 'Tagged': []}, replacements=[
                ('rule Tagged/main: x c\n  -- if c = RED', 'rule Tagged/main: x RED')]))
        self.assertEqual(report['projection']['Tagged'], [])
        self.assertEqual(report['projection']['Pre'], [0])

    def test_computed_helper_return_requires_its_unobserved_operand(self):
        model = self.analysis_model('output_uses.watsup',
            external={'Pair': [0], 'Tagged': []}, replacements=[
                ('relation Pre: nat nat hint(input %0)',
                 'relation Computed: nat nat hint(input %0)\n'
                 'rule Computed/main: x $(u + 1)\n  -- Pair: x y u\n\n'
                 'relation Pre: nat nat hint(input %0)'),
                ('  -- Pair: x y u\n  -- Tagged: x c\n  -- if z = y',
                 '  -- Computed: x z')])
        with self.assertRaises(CompileError) as caught:
            analyze_replay(model)
        self.assertIn('Pre -> Computed', str(caught.exception))
        self.assertIn('producer Pair output slot 1', str(caught.exception))


if __name__ == '__main__':
    unittest.main()
