"""Lean-resolved dependency closure and import edges used by certification."""
from pathlib import Path
import tempfile
import unittest

from tests import ROOT, SCRATCH
from pbt.lean_tools import fingerprint_dependencies, rebuild_modules
from translator.toolchain import digest


class LeanDependencyTests(unittest.TestCase):
    def test_fingerprints_include_transitive_sources_objects_and_import_edges(self):
        with tempfile.TemporaryDirectory(prefix='DependencyGraph', dir=SCRATCH) as tmp:
            root = Path(tmp)
            base = '.'.join(root.relative_to(ROOT).parts)
            leaf = root/'Leaf.lean'
            wrapper = root/'Wrapper.lean'
            leaf.write_text('def dependencyValue : Nat := 3\n')
            wrapper.write_text(f'import {base}.Leaf\n')
            rebuild_modules(ROOT, [base+'.Wrapper'], 60)
            graph = {}
            files = fingerprint_dependencies(ROOT, [wrapper], 60, dependency_graph=graph)
            self.assertEqual(files[str(leaf)], digest(leaf))
            self.assertIn(str(leaf), graph[str(wrapper)])
            self.assertTrue(any(name.endswith('/Leaf.olean') for name in files))
            leaf.write_text('def dependencyValue : Nat := 4\n')
            self.assertNotEqual(files[str(leaf)], digest(leaf))
