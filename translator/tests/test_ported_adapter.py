"""Regression cases for differences in current IL metadata and donor assumptions."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
CLI = ROOT / 'translator/_build/default/main.exe'
ORACLE = ROOT / 'translator/_build/default/tests/reference.exe'


class AdapterBoundaryTests(unittest.TestCase):
    def source(self, text):
        temporary = tempfile.TemporaryDirectory(dir=ROOT / 'translator')
        self.addCleanup(temporary.cleanup)
        source = Path(temporary.name) / 'spec.spectec'
        source.write_text(text)
        return source

    def translate(self, source, *flags):
        output = source.with_suffix('.lean')
        result = subprocess.run([str(CLI), '--backend', 'ported', '--namespace', 'Boundary',
            '--output', str(output), *flags, str(source)], cwd=ROOT,
            text=True, capture_output=True)
        return output, result

    def test_natural_negation_membership_uses_integer_runtime_value(self):
        source = self.source('''var n : nat
relation NegativeNatural: nat ==> bool hint(input %0)
rule NegativeNatural: n ==> ($(-n) <: nat)
''')
        output, result = self.translate(source)
        self.assertEqual(result.returncode, 0, result.stderr)
        oracle = subprocess.run([str(ORACLE), str(source), 'NegativeNatural', '[2]'],
            cwd=ROOT, text=True, capture_output=True)
        self.assertEqual(oracle.returncode, 0, oracle.stderr)
        self.assertEqual(json.loads(oracle.stdout), [False])
        with output.open('a') as stream:
            stream.write('''
open Boundary SpecTecExecution
example : runEval specTecExecutableProgram (PrimitiveRunner.unavailable _) 100
  (.call (SpecTecCall.NegativeNatural 2)) 0 = .done (.success false) 0 := by decide
example : runEval specTecExecutableProgram (PrimitiveRunner.unavailable _) 100
  (.call (SpecTecCall.NegativeNatural 0)) 0 = .done (.success true) 0 := by decide
''')
        check = subprocess.run(['lake', 'env', 'lean', str(output)], cwd=ROOT,
                               text=True, capture_output=True)
        self.assertEqual(check.returncode, 0, check.stdout + check.stderr)

    def test_composite_with_inconsistent_runtime_type_is_rejected(self):
        source = self.source('''var n : nat
relation NegativePair: nat ==> bool hint(input %0)
rule NegativePair: n ==> (($(-n), n) <: (nat, nat))
''')
        output, result = self.translate(source)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('runtime type', result.stderr)
        self.assertFalse(output.exists())

    def test_update_with_inconsistent_runtime_type_is_rejected(self):
        source = self.source('''var n : nat
var k : nat
relation NegativeList: nat*; nat ==> bool hint(input %0 %1)
rule NegativeList: n*; k ==> (((n*)[[0] = $(-k)]) <: nat*)
''')
        output, result = self.translate(source)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('runtime type', result.stderr)
        self.assertFalse(output.exists())

    def test_invalid_utf8_text_literal_is_rejected_before_writing(self):
        source = self.source(r'''var s : text
relation ByteLength: text ==> nat hint(input %0)
rule ByteLength: s ==> |"\C3"|
''')
        oracle = subprocess.run([str(ORACLE), str(source), 'ByteLength', '[""]'],
            cwd=ROOT, text=True, capture_output=True)
        self.assertEqual(oracle.returncode, 0, oracle.stderr)
        self.assertEqual(json.loads(oracle.stdout), [1])
        output, result = self.translate(source)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('UTF-8', result.stderr)
        self.assertFalse(output.exists())

    def test_valid_utf8_byte_escapes_preserve_byte_length(self):
        source = self.source(r'''var s : text
relation ByteLength: text ==> nat hint(input %0)
rule ByteLength: s ==> |"\C3\A9"|
''')
        output, result = self.translate(source)
        self.assertEqual(result.returncode, 0, result.stderr)
        with output.open('a') as stream:
            stream.write('''
open Boundary SpecTecExecution
example : runEval specTecExecutableProgram (PrimitiveRunner.unavailable _) 100
  (.call (SpecTecCall.ByteLength "")) 0 = .done (.success 2) 0 := by decide
''')
        check = subprocess.run(['lake', 'env', 'lean', str(output)], cwd=ROOT,
                               text=True, capture_output=True)
        self.assertEqual(check.returncode, 0, check.stdout + check.stderr)

    def test_donor_bits_builtin_requires_boolean_list_representation(self):
        source = self.source('''syntax bits = nat*
builtin dec $bits_to_int_unsigned(bits) : int
relation Bits: bits ==> int hint(input %0)
rule Bits: bits ==> $bits_to_int_unsigned(bits)
''')
        output, result = self.translate(source, '--builtin-profile', 'donor')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('bits', result.stderr)
        self.assertFalse(output.exists())

    def test_donor_bits_builtin_accepts_valid_representation(self):
        source = self.source('''syntax bits = bool*
builtin dec $bits_to_int_unsigned(bits) : int
relation Bits: bits ==> int hint(input %0)
rule Bits: bits ==> $bits_to_int_unsigned(bits)
''')
        output, result = self.translate(source, '--builtin-profile', 'donor')
        self.assertEqual(result.returncode, 0, result.stderr)
        with output.open('a') as stream:
            stream.write('''
open Boundary SpecTecExecution
example : runEval specTecExecutableProgram (PrimitiveRunner.unavailable _) 100
  (.call (SpecTecCall.Bits [true, false, true])) 0 = .done (.success 5) 0 := by decide
''')
        check = subprocess.run(['lake', 'env', 'lean', str(output)], cwd=ROOT,
                               text=True, capture_output=True)
        self.assertEqual(check.returncode, 0, check.stdout + check.stderr)
