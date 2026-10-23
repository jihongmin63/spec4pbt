"""Native helper extensions reuse the imported ordered specification semantics."""
from pathlib import Path
import subprocess
import tempfile
import unittest

from scripts.toolchain import resolve_toolchain
from scripts.tests import ROOT, SCRATCH

BASE = '''var n : nat

relation Accept:
  |- nat
  hint(input %0)
rule Accept/value:
  |- n

relation Never:
  |- nat
  hint(input %0)
rule Never/zero:
  |- n
  -- if $(n < 0)
'''
HELPERS = '''relation Probe:
  |- nat
  hint(input %0)
rule Probe/value:
  |- n
  -- Accept: |- n

relation Again:
  |- nat
  hint(input %0)
rule Again/value:
  |- n
  -- Probe: |- n

relation Rejected:
  |- nat
  hint(input %0)
rule Rejected/value:
  |- n
  -- Never:/ |- n
'''


FRESH_BASE = BASE + '''syntax typeId = text
var id : typeId
builtin dec $fresh_typeId() : typeId
builtin dec $text_to_int(text) : int

relation Advance:
  nat ~> typeId
  hint(input %0)
rule Advance/value:
  n ~> $fresh_typeId()

relation Crash:
  |- nat
  hint(input %0)
rule Crash/value:
  |- n
  -- if id = $fresh_typeId()
  -- if 0 = $text_to_int("bad")
'''
FRESH_HELPERS = HELPERS + '''relation Tick:
  nat ~> typeId
  hint(input %0)
rule Tick/value:
  n ~> id
  -- Advance: n ~> id

relation Pair:
  nat ~> typeId ':' typeId
  hint(input %0)
rule Pair/value:
  n ~> id_a ':' id_b
  -- Tick: n ~> id_a
  -- Tick: n ~> id_b

relation CrashProbe:
  |- nat
  hint(input %0)
rule CrashProbe/value:
  |- n
  -- Crash: |- n

relation CrashRejected:
  |- nat
  hint(input %0)
rule CrashRejected/value:
  |- n
  -- CrashProbe:/ |- n
'''

EXECUTION_TACTIC = '''
open SpecTec SpecTecExecution
syntax "prove_shared_execution" : tactic
macro_rules
  | `(tactic| prove_shared_execution) => `(tactic|
      first
        | exact Eval.pure _
        | exact Eval.freshId
        | exact Eval.unmatch
        | exact Eval.abort _
        | apply Eval.guard_true; decide
        | apply Eval.guard_false; decide
        | apply Eval.call; prove_shared_execution
        | apply Eval.orElse_success; prove_shared_execution
        | apply Eval.orElse_unmatch; prove_shared_execution; prove_shared_execution
        | apply Eval.orElse_abort; prove_shared_execution
        | apply Eval.bind_success; prove_shared_execution; prove_shared_execution
        | apply Eval.bind_unmatch; prove_shared_execution
        | apply Eval.bind_abort; prove_shared_execution
        | apply Eval.notHold_success; prove_shared_execution
        | apply Eval.notHold_unmatch; prove_shared_execution
        | apply Eval.notHold_abort; prove_shared_execution)
'''


class NativeSharedHelperTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.translator = resolve_toolchain(ROOT).executable

    def translate(self, *arguments):
        return subprocess.run([str(self.translator), *map(str, arguments)],
                              cwd=ROOT, capture_output=True, text=True, timeout=120)

    def test_helpers_share_base_types_and_preserve_ordered_outcomes(self):
        # A duplicate runtime, dropped delegation, or negation of logical absence
        # instead of normal unmatch breaks compilation of these checked proofs.
        with tempfile.TemporaryDirectory(prefix='NativeShared', dir=SCRATCH) as tmp:
            folder = Path(tmp)
            module = 'build.scratch.' + folder.name
            spec = folder / 'base.watsup'
            helpers = folder / 'helpers.watsup'
            spec.write_text(BASE)
            helpers.write_text(HELPERS)
            base = self.translate(spec)
            self.assertEqual(base.returncode, 0, base.stderr)
            (folder / 'Spec.lean').write_text(base.stdout)
            result = self.translate('--extension-base', module + '.Spec',
                                    '--extension-helper', 'Probe',
                                    '--extension-helper', 'Again',
                                    '--extension-helper', 'Rejected', spec, helpers)
            self.assertEqual(result.returncode, 0, result.stderr)
            (folder / 'Helpers.lean').write_text(result.stdout)
            proof = f'''import {module}.Helpers
open SpecTec SpecTecExecution

example : Again 7 := by
  refine ⟨0, ?_⟩
  exact .orElse_success (.bind_success
    (.orElse_success (.bind_success
      (.call (.orElse_success (.pure ()))) (.pure ()))) (.pure ()))

example : Rejected 7 := by
  refine ⟨0, ?_⟩
  exact .orElse_success (.bind_success
    (.notHold_success (.call (.orElse_unmatch
      (.bind_unmatch (.guard_false (by decide))) .unmatch))) (.pure ()))
'''
            (folder / 'Proof.lean').write_text(proof)
            build = subprocess.run(['lake', 'build', module + '.Proof'], cwd=ROOT,
                                   capture_output=True, text=True, timeout=120)
            self.assertEqual(build.returncode, 0, build.stdout + build.stderr)
            repeat = self.translate('--extension-base', module + '.Spec',
                                    '--extension-helper', 'Probe',
                                    '--extension-helper', 'Again',
                                    '--extension-helper', 'Rejected', spec, helpers)
            self.assertEqual(repeat.stdout, result.stdout)

    def test_extension_matches_combined_success_failure_abort_and_fresh_supply(self):
        # Both translation modes must prove these independently specified
        # outcomes. Resetting supply at an inlined call or treating abort as
        # ordinary failure makes at least one checked theorem impossible.
        with tempfile.TemporaryDirectory(prefix='NativeSharedOutcomes', dir=SCRATCH) as tmp:
            folder = Path(tmp)
            module = 'build.scratch.' + folder.name
            spec, helpers = folder / 'base.watsup', folder / 'helpers.watsup'
            spec.write_text(FRESH_BASE)
            helpers.write_text(FRESH_HELPERS)
            extension_args = ['--extension-base', module + '.Spec']
            for name in ['Probe', 'Again', 'Rejected', 'Tick', 'Pair',
                         'CrashProbe', 'CrashRejected']:
                extension_args += ['--extension-helper', name]
            for name, args in [('Spec', [spec]), ('Combined', [spec, helpers]),
                               ('Helpers', [*extension_args, spec, helpers])]:
                result = self.translate(*args)
                self.assertEqual(result.returncode, 0, result.stderr)
                (folder / (name + '.lean')).write_text(result.stdout)
            for imported, request in [
                ('Helpers', 'CrashRejected_plan 7'),
                ('Combined', 'Plan.call ⟨Unit, SpecTecCall.CrashRejected 7⟩'),
            ]:
                proof = ('import ' + module + '.' + imported + '\n' + EXECUTION_TACTIC
                         + '''
example : Again 7 := by refine ⟨0, ?_⟩; prove_shared_execution
example : Rejected 7 := by refine ⟨0, ?_⟩; prove_shared_execution
example : Pair 7 "FRESH__0" "FRESH__1" := by
  refine ⟨2, ?_⟩; prove_shared_execution
''' + f'''
example : Eval specTecProgram ({request}) 0
    (.abort "builtin $text_to_int failed") 1 := by prove_shared_execution
''')
                (folder / (imported + 'Proof.lean')).write_text(proof)
            result = subprocess.run(['lake', 'build', module + '.HelpersProof',
                                     module + '.CombinedProof'], cwd=ROOT,
                                    capture_output=True, text=True, timeout=120)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_recursive_helper_extension_is_rejected(self):
        with tempfile.TemporaryDirectory(prefix='NativeSharedCycle', dir=SCRATCH) as tmp:
            folder = Path(tmp)
            spec = folder / 'base.watsup'
            helpers = folder / 'helpers.watsup'
            spec.write_text(BASE)
            helpers.write_text('''relation Loop:
  |- nat
  hint(input %0)
rule Loop/value:
  |- n
  -- Loop: |- n
''')
            result = self.translate('--extension-base', 'Shared.Spec',
                                    '--extension-helper', 'Loop', spec, helpers)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('recursive helper', result.stderr)


if __name__ == '__main__':
    unittest.main()
