"""Check multiple translated helper publications with real Coq and pass evidence."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts import check, translate
from scripts.property.bridge import PINNED, build_bridge


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
import run as runner


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class CandidateNamespaceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.run_dir = Path(tempfile.mkdtemp(prefix='candidate-namespaces.',
                                       dir=ROOT / '_opam-testing-theorems/checks'))
        cls.backend, _ = translate.prepare_backend(PINNED, cls.run_dir)
        cls.invoke(['frontend', 'dune', 'build', '--root', str(cls.backend),
                    '-j', '2', 'p4spec/al_to_coq/main.exe'], 'build', timeout=240)
        cls.executable = cls.backend / '_build/default/p4spec/al_to_coq/main.exe'
        cls.bridge = build_bridge()

    @classmethod
    def invoke(cls, args, label, timeout=120):
        result = subprocess.run(['bash', str(ROOT / 'environment/env.sh'), *args],
                                cwd=cls.run_dir, capture_output=True, text=True,
                                timeout=timeout)
        log = Path(tempfile.mkdtemp(prefix=label + '.', dir=cls.run_dir)) / 'output.log'
        log.write_text(result.stdout + result.stderr)
        if result.returncode:
            raise AssertionError(f'{label}: {result.stdout}{result.stderr}')
        return result.stdout

    def setUp(self):
        self.directory = Path(tempfile.mkdtemp(prefix='case-', dir=self.run_dir))
        self.prop = self.directory / 'property'
        self.spec = self.directory / 'specification'
        self.prop.mkdir()
        (self.prop / 'Original.v').write_text('''From QuickChick Require Import QuickChick.
Definition Input := nat.
Definition encode_input (x : Input) : string := show x.
Inductive predicate : Input -> Prop := | any : forall (x : nat), predicate x.
''')
        self.candidate('v001', 'Property.Original')
        self.candidate('v002', 'Property.candidates.v001.Candidate', helper=True)
        self.candidate('v003', 'Property.candidates.v002.Candidate', helper=True)

    def publish(self, source, destination, profile, namespace):
        destination.mkdir(parents=True, exist_ok=True)
        backend_manifest = destination / 'backend.json'
        self.invoke(['frontend', str(self.executable), '--profile', profile,
                     '--input', str(source), '--output', str(destination),
                     '--manifest', str(backend_manifest)], f'generate-{profile}')
        (destination / 'frontend-al.txt').write_text(
            self.invoke(['frontend', str(self.bridge), 'dump', str(source)],
                        f'frontend-{profile}'))
        translator_hash = hashlib.sha256(b''.join(
            p.read_bytes() for p in sorted((ROOT / 'translator/src').glob('*.ml')))).hexdigest()
        manifest = {
            'namespace': namespace, 'profile': profile,
            'source': os.path.relpath(source, destination),
            'source_sha256': sha256(source),
            'translator_sha256': translator_hash,
            'frontend_al_sha256': sha256(destination / 'frontend-al.txt'),
            'backend_manifest_sha256': sha256(backend_manifest),
            'artifacts': [{'path': name, 'sha256': sha256(destination / name)}
                          for name in ['frontend-al.txt', 'backend.json']],
            'generated': json.loads(backend_manifest.read_text())['output_files'],
        }
        (destination / 'PassEvidence.json').write_text(json.dumps(manifest, indent=2) + '\n')

    def candidate(self, version, previous, helper=False):
        path = self.prop / 'candidates' / version
        path.mkdir(parents=True)
        imports = f'Require Import Property.Original {previous}.\n'
        if helper:
            namespace = f'Candidate{version.capitalize()}Spec'
            profile = f'candidate_{version}'
            source = path / 'Helper.watsup'
            source.write_text('var n : nat\nrelation Helper: nat nat hint(input %0)\n'
                              'rule Helper/main: n n\n')
            destination = self.spec / 'candidates' / version
            self.publish(source, destination, profile, namespace)
            imports += (f'From {namespace}.Generated Require Import InductiveRelations_0000.\n'
                        'From ALCoq Require Import Execution.\n')
            predicate = f'''Inductive predicate : Original.Input -> Prop :=
| step : forall (x y : nat) (final : State),
    {previous}.predicate x ->
    g_candidate_x5f_{version}_rel_Helper_execute x {{| next_fresh := 0 |}} (Success y) final ->
    predicate x.
'''
            proof = f'''Proof.
  intro x; split; intro H.
  - eapply Property.candidates.{version}.Candidate.step; [exact H | constructor].
  - inversion H; subst; assumption.
Qed.
'''
        else:
            predicate = ('Inductive predicate : Original.Input -> Prop :=\n'
                         '| any : forall (x : nat), predicate x.\n')
            proof = 'Proof. intro x; split; intro H; constructor. Qed.\n'
        (path / 'Candidate.v').write_text(imports + predicate)
        (path / 'Equivalence.v').write_text(
            imports + f'Require Property.candidates.{version}.Candidate.\n'
            f'Theorem equivalent : forall x, {previous}.predicate x <->\n'
            f'  Property.candidates.{version}.Candidate.predicate x.\n' + proof)

    def test_multiple_helper_namespaces_keep_separate_pass_evidence(self):
        session = check.Session(self.prop, fixture_root=self.spec)
        session.check()
        self.assertEqual(session.report['assumptions'], [])
        for version in ['v002', 'v003']:
            namespace = f'Candidate{version.capitalize()}Spec'
            target = f'candidate_{version}'
            self.assertIn(namespace, session.coq_flags)
            for name in ['PassEvidence.json', 'frontend-al.txt', 'backend.json',
                         'Generated/InductiveRelations_0000.v']:
                self.assertIn(f'{target}/{name}', session.report['source_hashes'])
            self.assertIn(f'property/candidates/{version}/Helper.watsup',
                          session.report['source_hashes'])
        self.assertEqual(len(session.report['semantic_publications']), 2)

    def test_primary_publication_selects_its_profile_namespace(self):
        source = self.prop / 'candidates/v002/Helper.watsup'
        self.publish(source, self.spec, 'p4', 'P4Spec')
        original = self.prop / 'Original.v'
        original.write_text('From P4Spec.Generated Require Import InductiveRelations_0000.\n' +
                            original.read_text())
        session = check.Session(self.prop, fixture_root=self.spec)
        session.check()
        self.assertEqual(session.report['assumptions'], [])
        self.assertEqual(session.report['namespace_mapping']['P4Spec']['snapshot'], 'fixture')
        self.assertIn('fixture/Generated/InductiveRelations_0000.v',
                      session.report['source_hashes'])

    def test_generator_kernel_check_uses_candidate_namespaces(self):
        session = check.Session(self.prop, selected='v003', fixture_root=self.spec)
        runner.execute(session, 'v003', 1, 3, 0, derive_only=True)
        self.assertEqual(session.report['generator_factory_assumptions'], [])
        self.assertEqual(session.report['generator_proof'], 'not_checked')
        self.assertTrue((session.sources / 'generator.ml').is_file())

    def test_new_publication_requires_both_pass_artifacts(self):
        manifest = self.spec / 'candidates/v002/PassEvidence.json'
        evidence = json.loads(manifest.read_text())
        evidence['artifacts'] = evidence['artifacts'][:1]
        manifest.write_text(json.dumps(evidence))
        session = check.Session(self.prop, fixture_root=self.spec)
        with self.assertRaisesRegex(check.CheckError, 'Missing semantic pass artifacts'):
            session.snapshot()

    def test_pass_artifacts_cannot_add_unchecked_coq(self):
        directory = self.spec / 'candidates/v002'
        injected = directory / 'Injected.v'
        injected.write_text('Axiom unchecked : False.\n')
        manifest = directory / 'PassEvidence.json'
        evidence = json.loads(manifest.read_text())
        evidence['artifacts'].append({'path': 'Injected.v', 'sha256': sha256(injected)})
        manifest.write_text(json.dumps(evidence))
        session = check.Session(self.prop, fixture_root=self.spec)
        with self.assertRaisesRegex(check.CheckError, 'Invalid semantic pass artifact'):
            session.snapshot()

    def test_prefix_does_not_depend_on_later_candidate_publication(self):
        # An invalid future manifest must not prevent checking the selected prefix.
        (self.spec / 'candidates/v003/PassEvidence.json').write_text('invalid later manifest')
        session = check.Session(self.prop, selected='v002', fixture_root=self.spec)
        session.check()
        self.assertEqual(session.report['assumptions'], [])
        self.assertFalse(any('v003' in path for path in session.report['source_hashes']))

    def test_tampered_pass_artifact_is_rejected_before_coq(self):
        (self.spec / 'candidates/v002/frontend-al.txt').write_text('changed pass output')
        session = check.Session(self.prop, fixture_root=self.spec)
        with self.assertRaisesRegex(check.CheckError, 'pass artifact changed'):
            session.snapshot()
        self.assertFalse(session.report['commands'])

    def test_pass_artifact_change_after_snapshot_is_rejected(self):
        session = check.Session(self.prop, fixture_root=self.spec)
        session.snapshot()
        (self.spec / 'candidates/v002/backend.json').write_text('{}')
        with self.assertRaisesRegex(check.CheckError, 'Source changed'):
            session.fresh()

    def test_unlisted_import_cannot_bypass_publication_hashes(self):
        root = self.spec / 'candidates/v002'
        (root / 'Injected.v').write_text('Definition outside_pass : nat := 0.\n')
        candidate = self.prop / 'candidates/v002/Candidate.v'
        original = candidate.read_text()
        for namespace in ['CandidateV002Spec', 'FixtureSpec.candidates.v002']:
            with self.subTest(namespace=namespace):
                candidate.write_text(f'From {namespace} Require Import Injected.\n' + original)
                session = check.Session(self.prop, fixture_root=self.spec)
                with self.assertRaisesRegex(check.CheckError, 'not listed.*semantic pass'):
                    session.snapshot()


if __name__ == '__main__':
    unittest.main()
