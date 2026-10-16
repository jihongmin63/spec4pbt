"""The port must be reachable without changing existing observation artifacts."""
import os
import pathlib
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
TRANSLATOR = ROOT / 'translator/_build/default/main.exe'
SOURCE = ROOT / 'external/spectecx/spectec/specs/itpl/ae/spec.spectec'


class PortCliTests(unittest.TestCase):
    def invoke(self, *options):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        output = pathlib.Path(temporary.name) / 'Generated.lean'
        command = [str(TRANSLATOR), '--namespace', 'Ported.Ae', '--output', str(output)]
        result = subprocess.run(command + list(options) + [str(SOURCE)],
                                cwd=ROOT, capture_output=True, text=True)
        return output, result

    def test_ported_backend_accepts_native_source_without_manifest(self):
        output, result = self.invoke('--backend', 'ported')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        with output.open('a') as stream:
            stream.write('\n#check Ported.Ae.Eval_expr\n')
        check = subprocess.run(['lake', 'env', 'lean', str(output)], cwd=ROOT,
                               capture_output=True, text=True)
        self.assertEqual(check.returncode, 0, check.stdout + check.stderr)

    def test_observation_backend_still_requires_manifest(self):
        output, result = self.invoke()
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(output.exists())

    def test_unknown_backend_writes_nothing(self):
        output, result = self.invoke('--backend', 'typo')
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(output.exists())

    def test_ported_backend_rejects_manifest_without_partial_artifacts(self):
        with tempfile.TemporaryDirectory() as directory:
            manifest = pathlib.Path(directory) / 'manifest.json'
            output, result = self.invoke('--backend', 'ported', '--manifest', str(manifest))
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('manifest', result.stderr.lower())
            self.assertFalse(output.exists())
            self.assertFalse(manifest.exists())

    def test_declarative_requires_ported_backend(self):
        output, result = self.invoke('--declarative')
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(output.exists())

    def test_independent_namespaces_coexist_and_preserve_text(self):
        # Global text replacement would corrupt the payload; embedding donor
        # runtime/prelude declarations would make the two imports collide.
        with tempfile.TemporaryDirectory() as directory:
            directory = pathlib.Path(directory)
            source = directory / 'text.spectec'
            source.write_text('''var t : text
relation Value: text ==> text hint(input %0)
rule Value:
  t ==> "SpecTec.literal"
''')
            for name in ['First', 'Second']:
                output = directory / (name + '.lean')
                result = subprocess.run([str(TRANSLATOR), '--backend', 'ported',
                    '--namespace', name + '.Spec', '--output', str(output), str(source)],
                    cwd=ROOT, capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                with output.open('a') as stream:
                    stream.write(f'''
example : SpecTecExecution.runEval {name}.Spec.specTecExecutableProgram
  (SpecTecExecution.PrimitiveRunner.unavailable {name}.Spec.specTecExecutableProgram)
  100 (.call ({name}.Spec.SpecTecCall.Value "ignored")) 0 =
  .done (.success "SpecTec.literal") 0 := by decide
''')
                result = subprocess.run(['lake', 'env', 'lean', '--root=' + str(directory), '-o',
                    str(output.with_suffix('.olean')), str(output)], cwd=ROOT,
                    capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            combined = directory / 'Together.lean'
            combined.write_text('import First\nimport Second\n'
                                '#check First.Spec.Value\n#check Second.Spec.Value\n')
            environment = os.environ.copy()
            environment['LEAN_PATH'] = str(directory) + os.pathsep + environment.get('LEAN_PATH', '')
            result = subprocess.run(['lake', 'env', 'lean', str(combined)], cwd=ROOT,
                                    env=environment, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
