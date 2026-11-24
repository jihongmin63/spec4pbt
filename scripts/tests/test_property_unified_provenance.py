"""Fixed publication and sample identities include the actual Coq source closure."""
from argparse import Namespace
from pathlib import Path
from types import SimpleNamespace
import importlib.util
import json
import sys
import tempfile
import unittest
from unittest.mock import patch

from scripts import check
from scripts.property import unified
from scripts.property.bridge import ROOT
from scripts.property.context import CONTEXT, file_hash


class UnifiedProvenanceTests(unittest.TestCase):
    def setUp(self):
        self.work = Path(tempfile.mkdtemp(prefix='unified-provenance.',
                                         dir=ROOT / '_opam-testing-theorems/checks'))
        self.prop = self.work / 'property'
        self.prop.mkdir()
        specification = self.work / 'specification'
        specification.mkdir()
        (specification / 'Spec.watsup').write_text('var n : nat\n')
        manifest = specification / 'Specification.toml'
        manifest.write_text('id="demo"\nsources=["Spec.watsup"]\nprofile="fixture"\n')
        (self.prop / 'Property.spectec').write_text(
            'property [identity]:\n  (x : nat)\n  true\n')
        self.prepared = unified.prepare_property(self.prop, manifest)
        candidate = self.prop / 'candidates/v001/Candidate.v'
        candidate.write_text('Require Import Specification.Helper.\n' + candidate.read_text())
        specification = self.work / 'specification'
        self.helper = specification / 'Helper.v'
        self.leaf = specification / 'Leaf.v'
        self.helper.write_text('From Specification Require Import Leaf.\n'
                               'Definition helper := leaf.\n')
        self.leaf.write_text('Definition leaf : nat := 1.\n')
        roots = check.namespace_roots
        def fixture_roots(*args, **kwargs):
            return {**roots(*args, **kwargs),
                    'Specification': (specification, Path('specification'))}
        self.root_patch = patch.object(check, 'namespace_roots', fixture_roots)
        self.root_patch.start()
        self.addCleanup(self.root_patch.stop)

    def batch(self):
        runs = self.prop / '.runs'
        runs.mkdir(exist_ok=True)
        directory = runs / 'sample'
        directory.mkdir()
        samples = directory / 'samples.json'
        samples.write_text(json.dumps([{'x': {'type': 'nat', 'value': '7'}}]) + '\n')
        batch = {'version': 2, 'candidate': 'v001',
                 'semantic_hashes': self.prepared.context['semantic_hashes'], 'tool_hashes': {},
                 'context_sha256': file_hash(runs / CONTEXT),
                 'candidate_hashes': unified.candidate_hashes(self.prop, 'v001'),
                 'samples_sha256': file_hash(samples)}
        (directory / 'batch.json').write_text(json.dumps(batch))
        return Namespace(input_json=None, samples_file=samples), SimpleNamespace(
            context={'semantic_hashes': batch['semantic_hashes']})

    def test_transitive_import_change_rejected_by_public_load_inputs(self):
        args, prepared = self.batch()
        self.assertEqual(unified.load_inputs(args, self.prop, prepared, {})[0],
                         [{'x': {'type': 'nat', 'value': '7'}}])
        for path in (self.helper, self.leaf):
            with self.subTest(dependency=path.name):
                before = path.read_text()
                path.write_text(before + '\n(* changed imported source *)\n')
                try:
                    with self.assertRaisesRegex(ValueError, 'candidate changed'):
                        unified.load_inputs(args, self.prop, prepared, {})
                finally:
                    path.write_text(before)

    def test_sampling_rejects_a_transient_dependency_change_in_real_derivation(self):
        from scripts.property.generation import GenerationBatch, load_samples
        spec = importlib.util.spec_from_file_location('unified_provenance_runner', ROOT / 'scripts/run.py')
        runner = importlib.util.module_from_spec(spec)
        with patch.dict(sys.modules, {'check': check}):
            spec.loader.exec_module(runner)
        before = self.leaf.read_text()
        def derive(property_dir, candidate, fields, **options):
            self.leaf.write_text('Definition leaf : nat := 2.\n')
            try:
                session = check.Session(property_dir, candidate)
                runner.execute(session, candidate, options['count'], options['size'], options['seed'])
                report = session.finish()
                samples = load_samples(json.loads((session.directory / 'samples.json').read_text()),
                                       fields, options['type_schema'])
                return GenerationBatch(candidate, tuple(samples), report,
                                       options['seed'], options['size'])
            finally:
                self.leaf.write_text(before)
        args = Namespace(property=self.prop, action='sample', spec=None,
                         candidate='v001', count=2, size=8, seed=7)
        with patch.object(unified, 'derive_and_sample', derive):
            path, ok = unified.execute(args)
        self.assertFalse(ok)
        report = json.loads(path.read_text())
        self.assertIn('sources changed between snapshot and derivation', report['error'])
        self.assertNotIn('samples_file', report)

    def test_debug_rechecks_transitive_sources_after_execution(self):
        args, _ = self.batch()
        args.property, args.action, args.spec = self.prop, 'debug', None
        args.implementation, args.timeout = None, 20
        # The batch fixture is independent of tool freshness; bind it to today's tools.
        batch_path = args.samples_file.parent / 'batch.json'
        batch = json.loads(batch_path.read_text())
        batch['tool_hashes'] = unified.tool_hashes()
        batch_path.write_text(json.dumps(batch))
        before, native_debug = self.leaf.read_text(), unified.debug
        def mutate_after_debug(*values, **options):
            result = native_debug(*values, **options)
            self.leaf.write_text(before + '\n(* changed during debug *)\n')
            return result
        try:
            with patch.object(unified, 'debug', mutate_after_debug):
                path, ok = unified.execute(args)
            self.assertFalse(ok)
            self.assertIn('candidate changed since sampling', json.loads(path.read_text())['error'])
        finally:
            self.leaf.write_text(before)

    def test_checker_compiles_same_transitive_closure_and_preserves_snapshot(self):
        session = check.Session(self.prop, 'v001')
        session.check()
        session.finish()
        self.assertEqual(session.report['status'], 'passed')
        identities = unified.candidate_hashes(self.prop, 'v001')
        for path in (self.helper, self.leaf):
            self.assertEqual(identities[str(path)], file_hash(path))
            snapshot = session.sources / 'specification' / path.name
            self.assertEqual(snapshot.read_bytes(), path.read_bytes())

    def test_base_publication_excludes_preexisting_candidate_sources(self):
        publication = self.work / 'publication'
        publication.mkdir()
        (publication / 'PassEvidence.json').write_text('{"artifacts": []}\n')
        fixed = publication / 'Generated/Fixed.v'
        fixed.parent.mkdir()
        fixed.write_text('Definition fixed := 1.\n')
        selected = publication / 'candidates/v001'
        selected.mkdir(parents=True)
        (selected / 'PassEvidence.json').write_text('{"artifacts": []}\n')
        candidate = selected / 'Candidate.v'
        candidate.write_text('Definition candidate := 1.\n')
        baseline = unified.publication_hashes(publication)
        candidate_before = unified.publication_hashes(selected)
        self.assertNotIn(str(candidate), baseline)
        self.assertIn(str(fixed), baseline)
        candidate.write_text('Definition candidate := 2.\n')
        self.assertEqual(unified.publication_hashes(publication), baseline)
        self.assertNotEqual(unified.publication_hashes(selected), candidate_before)


if __name__ == '__main__':
    unittest.main()
