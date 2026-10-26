"""Wasm lsl_ preserves the upstream clamp in native and generated Lean code."""
from pathlib import Path
import subprocess
import tempfile
import unittest

from scripts.tests import ROOT, FIXTURES, SCRATCH
from scripts.toolchain import resolve_toolchain


# Literal boundary cases, with powers used only to spell large expected values.
# Clamping to 2048, allowing negative shifts, or truncating OCaml-sized offsets
# changes these observable results.
CASES = [
    (3, -7, 3), (-3, -7, -3), (3, 0, 3), (-3, 0, -3),
    (3, 1, 6), (-3, 1, -6), (1, 4, 16), (1, 5, 32),
    (1, 4095, 2**4095), (1, 4096, 2**4096),
    (1, 4097, 2**4096), (-3, 4097, -3 * 2**4096),
    (1, 65536, 2**4096), (1, 2**128, 2**4096),
    (3, -(2**128), 3), (0, 2**128, 0),
]

NATIVE_PROBE = '''open Lang
open Xl
open Util.Source
module Calls = Builtin.Call.Make (Builtin.Call.No_ext) ()

let () =
  for i = 0 to (Array.length Sys.argv - 1) / 2 - 1 do
    let value index = Runtime.Value.Make.int (Bigint.of_string Sys.argv.(index)) in
    let added = ref 0 in
    let result = Calls.invoke (fun _ -> incr added) ("lsl_" $ no_region) []
      [value (1 + 2 * i); value (2 + 2 * i)] in
    if !added <> 1 then failwith "builtin must register its returned value";
    result |> Runtime.Value.Get.num |> Num.to_int |> Bigint.to_string |> print_endline
  done
'''


class LslBuiltinTests(unittest.TestCase):
    def setUp(self):
        self.tool = resolve_toolchain(ROOT)
        self.tmp = tempfile.TemporaryDirectory(prefix='LslBuiltin', dir=SCRATCH)
        self.addCleanup(self.tmp.cleanup)
        self.folder = Path(self.tmp.name)

    def run_command(self, args, *, cwd=ROOT):
        return subprocess.run(list(map(str, args)), cwd=cwd, text=True,
                              capture_output=True, timeout=120)

    def test_native_registered_builtin_matches_wasm_boundaries(self):
        # Link the real copied native library, including its public dispatcher.
        with tempfile.TemporaryDirectory(prefix='lsl-probe-', dir=self.tool.root / 'p4spec/lib') as tmp:
            probe = Path(tmp)
            (probe / 'probe.ml').write_text(NATIVE_PROBE)
            (probe / 'dune').write_text(
                '(executable (name probe) (libraries builtin runtime lang util))\n')
            target = probe.relative_to(self.tool.root) / 'probe.exe'
            built = self.run_command(['opam', 'exec', '--switch=' + self.tool.switch,
                                      '--', 'dune', 'build', '--root', self.tool.root, target])
            self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
            exe = self.tool.root / '_build/default' / target
            args = [str(value) for a, b, _ in CASES for value in (a, b)]
            actual = self.run_command([exe, *args])
            self.assertEqual(actual.returncode, 0, actual.stdout + actual.stderr)
            self.assertEqual([int(line) for line in actual.stdout.splitlines()],
                             [expected for _, _, expected in CASES])

    def test_generated_lean_builtin_and_ordered_execution_match_boundaries(self):
        result = self.run_command([self.tool.executable, FIXTURES / 'lsl.watsup'])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        proofs = ['\nopen SpecTecExecution\n']
        for a, b, expected in CASES:
            proofs.append(f'example : SpecTec.«$lsl_» ({a}) ({b}) = ({expected}) := by decide\n')
            # The ordered clause returns the builtin value without consuming supply.
            proofs.append(
                f'example : ∃ v, SpecTec.Shift ({a}) ({b}) v ∧ v = ({expected}) :=\n'
                '  ⟨_, ⟨0, .call (.orElse_success (.pure _))⟩, by decide⟩\n')
        path = self.folder / 'Check.lean'
        path.write_text(result.stdout + ''.join(proofs))
        checked = self.run_command(['lake', 'env', 'lean', path])
        self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)

    def test_polymorphic_lsl_signature_is_rejected(self):
        spec = self.folder / 'bad.watsup'
        spec.write_text('builtin dec $lsl_<X>(int, int) : int\n')
        result = self.run_command([self.tool.executable, spec])
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('number of type parameters is unexpected', result.stderr)


if __name__ == '__main__':
    unittest.main()
