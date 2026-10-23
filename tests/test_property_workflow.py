"""Public emit/edit/check/run lifecycle and its certification boundaries."""
import json
import os
from pathlib import Path
import tempfile
import unittest
import subprocess

from tests import ROOT, ORDERED, SCRATCH
from pbt.property import workflow
from pbt.property.clause import load_bundle
from pbt.property.runner import run_property


class PropertyWorkflowTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='Workflow', dir=SCRATCH)
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.base = '.'.join(self.root.relative_to(ROOT).parts)
        self.output = self.root / 'Bundle'
        self.contract = self.base + '.Bundle.Contract'
        self.arguments = dict(
            spec_paths=[ORDERED / 'spec.watsup'],
            property_path=ORDERED / 'properties.watsup',
            config_path=ORDERED / 'observations.toml',
            external_path=ORDERED / 'external/positive.toml',
            name='positive', output=self.output,
            proof_module=self.base + '.Proof', property_proof='ClauseCopy.property_correct',
            generator_module=self.base + '.Generator', generator='ClauseCopyGenerator.generator',
        )

    def emit(self):
        return workflow.emit_property(**self.arguments)

    def complete(self):
        proof = (ORDERED / 'templates/copy_positive_proof.lean.in').read_text()
        generator = (ORDERED / 'templates/copy_positive_generator.lean.in').read_text()
        (self.root / 'Proof.lean').write_text(proof.replace('@CONTRACT@', self.contract))
        (self.root / 'Generator.lean').write_text(generator.replace('@CONTRACT@', self.contract)
            .replace('@PROOF@', self.base + '.Proof'))

    def test_emit_exposes_both_obligations_without_certifying(self):
        self.assertEqual(self.emit(), self.output)
        self.assertIn('abbrev generator := CorrectGen Premise',
                      (self.output / 'Contract.lean').read_text())
        self.assertIn('Contract.property := by', (self.root / 'Proof.lean').read_text())
        self.assertIn('Contract.generator := by', (self.root / 'Generator.lean').read_text())
        self.assertNotIn('sorry', (self.root / 'Proof.lean').read_text())
        self.assertTrue((self.output / 'ContractAudit.lean').exists())
        self.assertIn('generator', (self.output / 'GeneratorAudit.lean').read_text())
        self.assertFalse((self.output / 'certificate.json').exists())
        with self.assertRaisesRegex((ValueError, OSError), 'check|certificate'):
            load_bundle(self.output)

    def test_reemit_preserves_authored_sources_and_unrelated_files(self):
        self.emit()
        self.complete()
        before = {name: (self.root / name).read_bytes() for name in ['Proof.lean', 'Generator.lean']}
        (self.output / 'notes.txt').write_text('keep')
        (self.output / 'certificate.json').write_text('{}')
        self.emit()
        for name, source in before.items():
            self.assertEqual((self.root / name).read_bytes(), source)
        self.assertEqual((self.output / 'notes.txt').read_text(), 'keep')
        self.assertFalse((self.output / 'certificate.json').exists())

    def test_reemit_does_not_follow_generated_file_hardlinks(self):
        self.emit()
        authored = self.root / 'kept-source.txt'
        authored.write_text('keep authored content')
        generated = self.output / 'Spec.lean'
        generated.unlink()
        os.link(authored, generated)
        self.emit()
        self.assertEqual(authored.read_text(), 'keep authored content')

    def test_reemit_rejects_generated_file_symlinks(self):
        self.emit()
        authored = self.root / 'kept-source.txt'
        authored.write_text('keep authored content')
        generated = self.output / 'Spec.lean'
        generated.unlink()
        generated.symlink_to(authored)
        with self.assertRaisesRegex(ValueError, 'regular file'):
            self.emit()
        self.assertEqual(authored.read_text(), 'keep authored content')

    def test_templates_fail_check_and_survive_failure(self):
        self.emit()
        with self.assertRaisesRegex(ChildProcessError, 'complete|unsolved|Fill'):
            workflow.check_property(self.output)
        self.assertTrue((self.root / 'Proof.lean').exists())
        self.assertTrue((self.output / 'Contract.lean').exists())
        self.assertFalse((self.output / 'certificate.json').exists())

    def test_invalid_check_timeout_invalidates_previous_certificate(self):
        self.emit()
        certificate = self.output / 'certificate.json'
        certificate.write_text('{}')
        with self.assertRaisesRegex(ValueError, 'finite and positive'):
            workflow.check_property(self.output, timeout_seconds=0)
        self.assertFalse(certificate.exists())

    def test_check_reconstructs_contract_even_if_emission_hash_is_changed(self):
        self.emit()
        contract = self.output / 'Contract.lean'
        contract.write_text(contract.read_text().replace('CorrectGen Premise', 'Nat'))
        from translator.toolchain import digest
        metadata = self.output / 'emission.json'
        record = json.loads(metadata.read_text())
        record['generated']['Contract.lean'] = digest(contract)
        metadata.write_text(json.dumps(record))
        with self.assertRaisesRegex(ValueError, 'generated.*mismatch|contract.*mismatch'):
            workflow.check_property(self.output)
        self.assertFalse((self.output / 'certificate.json').exists())

    def test_joint_check_run_and_freshness(self):
        self.emit()
        self.complete()
        bundle = workflow.check_property(self.output)
        cert = json.loads((self.output / 'certificate.json').read_text())
        self.assertEqual(cert['schema_version'], 4)
        self.assertEqual(cert['generator'], 'ClauseCopyGenerator.generator')
        self.assertIn(str(self.root / 'Generator.lean'), cert['fingerprints'])
        changed_selection = {**cert, 'property_name': 'different_property'}
        (self.output / 'certificate.json').write_text(json.dumps(changed_selection))
        with self.assertRaisesRegex(ValueError, 'source selection'):
            load_bundle(self.output)
        (self.output / 'certificate.json').write_text(json.dumps(cert))
        loaded = load_bundle(self.output)
        result = run_property(loaded, implementation=ORDERED / 'implementations/correct.toml',
                              output=self.root / 'results', count=2, size=6, seed=0)
        self.assertEqual((result.status, result.counts['pass']), ('passed', 2))
        with self.assertRaisesRegex(ValueError, 'certified generator'):
            run_property(bundle, generator_module=self.base + '.Generator', generator='Other.generator',
                         implementation=ORDERED / 'implementations/correct.toml', output=self.root / 'wrong')
        file = self.root / 'Generator.lean'
        file.write_text(file.read_text() + '\n-- changed\n')
        with self.assertRaisesRegex(ValueError, 'stale'):
            load_bundle(self.output)
        file.write_text(f'import {self.contract}\n'
                        f'def ClauseCopyGenerator.generator : {self.contract}.generator := by sorry\n')
        from translator.toolchain import digest
        cert['fingerprints'][str(file)] = digest(file)
        (self.output / 'certificate.json').write_text(json.dumps(cert))
        with self.assertRaisesRegex(ChildProcessError, 'sorry|forbidden|axiom'):
            load_bundle(self.output)
        with self.assertRaisesRegex(ChildProcessError, 'sorry|forbidden|axiom'):
            workflow.check_property(self.output)
        self.assertFalse((self.output / 'certificate.json').exists())
        self.assertTrue((self.root / 'results/result.json').exists())

    def test_mismatched_generator_is_rejected_at_check(self):
        self.emit()
        self.complete()
        (self.root / 'Generator.lean').write_text(
            'import Spec4Pbt.CorrectGen\n'
            'def ClauseCopyGenerator.generator : CorrectGen (fun n : Nat => n = 0) :=\n'
            '  Gen.CorrectGen.s_pure 0\n')
        with self.assertRaisesRegex(ChildProcessError, 'type mismatch|expected exactly'):
            workflow.check_property(self.output)
        self.assertFalse((self.output / 'certificate.json').exists())

    def test_forged_certificate_cannot_skip_lean_audits(self):
        self.emit()
        emission = json.loads((self.output / 'emission.json').read_text())
        plan = json.loads((self.output / 'plan.json').read_text())
        forged = dict(schema_version=4, project=str(ROOT), module=self.contract,
            namespace=self.contract, plan_id=plan['plan_id'], fingerprints={},
            toolchain=emission['toolchain'], **emission['declarations'],
            spec_paths=emission['request']['spec_paths'],
            property_path=emission['request']['property_path'], property_name='positive')
        (self.output / 'certificate.json').write_text(json.dumps(forged))
        with self.assertRaises((ChildProcessError, ValueError)):
            load_bundle(self.output)

    def test_proof_cannot_import_generator_transitively(self):
        self.emit()
        self.complete()
        proof = (self.root / 'Proof.lean').read_text().replace('property_correct', 'helper_correct')
        generator = '\n'.join(line for line in (self.root / 'Generator.lean').read_text().splitlines()
                              if not line.startswith('import '))
        (self.root / 'Generator.lean').write_text(proof + '\n' + generator)
        (self.root / 'Helper.lean').write_text('import '+self.base+'.Generator\n')
        (self.root / 'Proof.lean').write_text(
            f'import {self.base}.Helper\n'
            f'theorem ClauseCopy.property_correct : {self.contract}.property := ClauseCopy.helper_correct\n')
        with self.assertRaisesRegex(ValueError, 'proof.*depend.*generator'):
            workflow.check_property(self.output)
        self.assertFalse((self.output / 'certificate.json').exists())

    def test_output_cannot_replace_authored_directory(self):
        args = {**self.arguments, 'output': ROOT / 'properties'}
        with self.assertRaisesRegex(ValueError, 'out|generated'):
            workflow.emit_property(**args)

    def test_legacy_build_preserves_frontend_error_diagnostic(self):
        from pbt.property.clause import build_property
        broken = self.root / 'broken.watsup'
        broken.write_text('not a valid SpecTec declaration\n')
        arguments = {key: value for key, value in self.arguments.items()
                     if key not in ('generator_module', 'generator')}
        arguments['property_path'] = broken
        with self.assertRaises(ChildProcessError):
            build_property(**arguments)
        self.assertFalse(self.output.exists())

    def test_cli_exposes_emit_check_and_run_uses_certificate_selection(self):
        command = ['python3', '-m', 'pbt.property', 'emit']
        for key, value in self.arguments.items():
            flag = {'spec_paths': '--spec', 'property_path': '--property',
                    'config_path': '--config', 'external_path': '--external'}.get(
                        key, '--' + key.replace('_', '-'))
            for item in value if isinstance(value, list) else [value]:
                command += [flag, str(item)]
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)['status'], 'emitted')
        check = subprocess.run(['python3', '-m', 'pbt.property', 'check', '--help'],
                               cwd=ROOT, capture_output=True, text=True)
        self.assertEqual(check.returncode, 0, check.stderr)
        run = subprocess.run(['python3', '-m', 'pbt.property', 'run', '--help'],
                             cwd=ROOT, capture_output=True, text=True)
        self.assertNotIn('--generator-module', run.stdout)
        old = subprocess.run(['python3', '-m', 'pbt.property', 'build', '--help'],
                             cwd=ROOT, capture_output=True, text=True)
        self.assertNotEqual(old.returncode, 0)


if __name__ == '__main__':
    unittest.main()
