"""Public Python module commands are invoked from the repository root."""
import subprocess
import sys
import unittest

from tests import ROOT


class EntrypointTests(unittest.TestCase):
    def test_property_commands_expose_their_interfaces(self):
        for action in ('inspect', 'plan', 'build', 'run', 'collect', 'recheck', 'rerun'):
            with self.subTest(action=action):
                result = subprocess.run(
                    [sys.executable, '-m', 'pbt.property', action, '--help'],
                    cwd=ROOT, text=True, capture_output=True, timeout=20)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn('usage:', result.stdout)
                if action in ('run', 'collect', 'rerun'):
                    self.assertIn('--implementation', result.stdout)

    def test_toolchain_commands_expose_help(self):
        for action in ('bootstrap', 'build', 'check'):
            with self.subTest(action=action):
                result = subprocess.run(
                    [sys.executable, '-m', 'translator.toolchain', action, '--help'],
                    cwd=ROOT, text=True, capture_output=True, timeout=20)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn('--project', result.stdout)
