"""Property predicates retain typed AL premise evaluation and fresh state."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts import check
from scripts.property import rocq
from scripts.property.compiler import compile_spec, compile_debug
from scripts.property.debug import debug
from scripts.property.generation import load_samples

ROOT = Path(__file__).resolve().parents[2]
FIXTURES = ROOT / 'scripts/tests/fixtures/property/rocq'
sys.path.insert(0, str(ROOT / 'scripts'))
import run as runner


class PropertyTranslationTests(unittest.TestCase):
    def derive(self, directory, source, config, publication, *, size=4):
        prop = directory / 'property'
        candidate = prop / 'candidates/v001'
        candidate.mkdir(parents=True)
        original = rocq.render_original(source, config, publication=publication)
        (prop / 'Original.v').write_text(original)
        declaration = original[original.index('Inductive predicate'):]
        declaration = declaration.split('From Coq Require Import String Ascii Bool ZArith DecimalString.')[0]
        namespace = rocq.publication_plan(publication)['namespace']
        (candidate / 'Candidate.v').write_text(
            'Require Import Property.Original.\n'
            'From Coq Require Import String ZArith.\n'
            'From ALCoq Require Import Execution.\n'
            f'From {namespace}.Generated Require Import Types_0000 InductiveRelations.\n' + declaration)
        (candidate / 'Equivalence.v').write_text('''Require Import Property.Original Property.candidates.v001.Candidate.
Theorem equivalent : forall x : Original.Input,
  Original.predicate x <-> Candidate.predicate x.
Proof.
  intro x; split; intro H; destruct H; econstructor; eassumption.
Qed.
''')
        session = check.Session(prop, selected='v001', fixture_root=publication, timeout=120)
        try:
            runner.execute(session, 'v001', 6, size, 0)
        except Exception as error:
            session.finish(error)
            raise
        session.finish()
        self.assertEqual(session.report['schedule_variables'], ['x'])
        self.assertEqual(session.report['generator_factory_assumptions'], [])
        self.assertEqual(session.report['generator_proof'], 'not_checked')
        model = compile_spec(source, config)
        samples = load_samples(json.loads((session.directory / 'samples.json').read_text()),
                               model.inputs, model.type_schema)
        self.assertTrue(any(sample is not None for sample in samples))
        return model, samples

    def test_multi_field_adt_input_is_derived_extracted_and_executed(self):
        directory = Path(tempfile.mkdtemp(dir=ROOT / '_opam-testing-theorems/checks',
                                         prefix='property-typed-generation-'))
        source = ROOT / 'scripts/tests/fixtures/property/bridge/typed_input.watsup'
        config = directory / 'Property.toml'
        config.write_text('precondition = "Pre"\ngoal = "Goal"\n')
        publication = rocq.translate_property(source, config, directory / 'spec')
        model, samples = self.derive(directory, source, config, publication)
        for sample in samples:
            if sample is not None:
                self.assertEqual(set(sample), {'t', 'n', 'i', 's', 'b'})
                self.assertEqual(debug(compile_debug(model), sample).status, 'passed')

    def test_condition_and_computed_return_use_temporary_relations(self):
        directory = Path(tempfile.mkdtemp(dir=ROOT / '_opam-testing-theorems/checks',
                                         prefix='property-computed-'))
        source = FIXTURES / 'computed.watsup'
        config = directory / 'Property.toml'
        config.write_text('precondition = "Pre"\ngoal = "Goal"\n')
        publication = rocq.translate_property(source, config, directory / 'spec')
        plan = rocq.publication_plan(publication)
        self.assertEqual(len(plan['calls']), 2)
        self.assertTrue(all(call['temporary'] for call in plan['calls']))
        model, samples = self.derive(directory, source, config, publication, size=16)
        for sample in samples:
            if sample is not None:
                self.assertEqual(sample['x']['value'], '7')
                self.assertEqual(debug(compile_debug(model), sample).status, 'failed')

    def test_negative_condition_derives_samples_with_closed_equivalence(self):
        directory = Path(tempfile.mkdtemp(dir=ROOT / '_opam-testing-theorems/checks',
                                         prefix='property-negative-generation-'))
        source = directory / 'Negative.watsup'
        source.write_text((ROOT / 'scripts/tests/fixtures/property/bridge/negation.watsup').read_text() + '''
relation Pre: |- nat hint(input %0)
rule Pre/main: |- x
  -- Zero:/ |- x
relation Goal: |- nat hint(input %0)
rule Goal/main: |- x
  -- Zero:/ |- x
''')
        config = directory / 'Property.toml'
        config.write_text('precondition = "Pre"\ngoal = "Goal"\n')
        publication = rocq.translate_property(source, config, directory / 'spec')
        plan = rocq.publication_plan(publication)
        self.assertEqual(len(plan['calls']), 1)
        self.assertTrue(plan['calls'][0]['temporary'])
        model, samples = self.derive(directory, source, config, publication, size=16)
        for sample in samples:
            if sample is not None:
                self.assertNotEqual(sample['x']['value'], '0')
                self.assertEqual(debug(compile_debug(model), sample).status, 'passed')

    def test_effectful_computed_return_keeps_fresh_state(self):
        directory = Path(tempfile.mkdtemp(dir=ROOT / '_opam-testing-theorems/checks',
                                         prefix='property-return-fresh-'))
        source = directory / 'ComputedFresh.watsup'
        source.write_text((FIXTURES / 'temporary.watsup').read_text().replace(
            'rule Pre/main: x z a b', 'rule Pre/main: x z a $fresh_typeId()').replace(
            '  -- if b = $fresh_typeId()\n', ''))
        config = directory / 'Property.toml'
        config.write_text('precondition = "Pre"\ngoal = "Goal"\n')
        publication = rocq.translate_property(source, config, directory / 'spec', profile='p4')
        model, samples = self.derive(directory, source, config, publication)
        for sample in samples:
            if sample is not None:
                result = debug(compile_debug(model), sample)
                self.assertEqual(result.status, 'failed')
                self.assertEqual([v['value'] for v in result.trace['pre_outputs'][1:]],
                                 ['FRESH__0', 'FRESH__1'])
                self.assertEqual(result.trace['fresh_id'], 2)

    def test_temporary_premises_are_translated_and_thread_fresh(self):
        directory = tempfile.mkdtemp(dir=ROOT / '_opam-testing-theorems/checks',
                                     prefix='property-temporary-')
        directory = Path(directory)
        config = directory / 'Property.toml'
        config.write_text('precondition = "Pre"\ngoal = "Goal"\n')
        publication = rocq.translate_property(FIXTURES / 'temporary.watsup', config,
                                              directory / 'spec', profile='p4')
        plan = rocq.publication_plan(publication)
        self.assertEqual([f['name'] for f in plan['inputs']], ['x'])
        self.assertGreaterEqual(sum(c['temporary'] for c in plan['calls']), 3)
        original = rocq.render_original(FIXTURES / 'temporary.watsup', config,
                                         publication=publication)
        self.assertNotIn('g_p4_rel_Goal_execute', original)
        self.assertIn('g_p4_rel_Step_execute', original)
        self.assertNotIn('Inductive g_p4_rel_Step_execute', original)
        compiled = json.loads((publication / json.loads((publication / 'PassEvidence.json').read_text())['evidence_dir'] / 'Compilation.json').read_text())
        # A closed concrete witness checks both the temporary AL rules and
        # the state carried through their successive fresh calls.
        (directory / 'Original.v').write_text(original)
        (directory / 'Check.v').write_text('''
From Coq Require Import String.
From ALCoq Require Import Execution Values.
From P4Spec.Generated Require Import InductiveRelations.
Require Import Original.
Open Scope string_scope.
Example generated_pre : predicate (mkInput 0).
Proof. econstructor; repeat econstructor. Qed.
Example source_pre : exists final,
  g_p4_rel_Pre_execute 0 {| next_fresh := 0 |}
(Success (3, "FRESH__0", "FRESH__1")) final.
Proof. eexists; repeat econstructor. Qed.
Theorem source_equivalent : forall x,
  predicate (mkInput x) <-> exists z a b final,
  g_p4_rel_Pre_execute x {| next_fresh := 0 |} (Success (z,a,b)) final.
Proof. intro x; split; intro H; repeat econstructor. Qed.
Print Assumptions source_equivalent.
Print Assumptions generated_pre.
Print Assumptions source_pre.
''')
        for file in ('Original.v', 'Check.v'):
            result = subprocess.run(
                ['bash', str(ROOT / 'environment/env.sh'), 'coqc', '-q',
                 '-Q', compiled['support'], 'ALCoq',
                 '-Q', compiled['spec'], 'P4Spec', file], cwd=directory,
                capture_output=True, text=True, timeout=120)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        # False Goal remains outside generator conditions.
        model, samples = self.derive(directory, FIXTURES / 'temporary.watsup', config, publication)
        for sample in samples:
            if sample is not None:
                self.assertEqual(debug(compile_debug(model), sample).status, 'failed')


if __name__ == '__main__':
    unittest.main()
