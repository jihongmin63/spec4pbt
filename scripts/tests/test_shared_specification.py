"""Reuse shared translation without trusting editable cache hash claims."""
import json
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import tempfile
import threading
import unittest
from unittest.mock import patch

from scripts.tests import ROOT, ORDERED, SCRATCH
from scripts.specification import prepare_translation
from scripts.toolchain import digest


class SharedSpecificationTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='SharedSpec', dir=SCRATCH)
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.spec = self.root/'spec.watsup'
        self.spec.write_bytes((ORDERED/'spec.watsup').read_bytes())
        self.catalog = self.root/'observations.toml'
        self.catalog.write_bytes((ORDERED/'observations.toml').read_bytes())

    def prepare(self, **kwargs):
        return prepare_translation([self.spec], self.catalog, project=ROOT, **kwargs)

    def test_reuses_translation_without_running_native_translator(self):
        first = self.prepare()
        with patch('scripts.specification.run_checked', side_effect=AssertionError('cache was not reused')):
            second = self.prepare()
        self.assertEqual(first, second)
        self.assertTrue((first.directory/'Spec.lean').is_file())

    def test_changed_source_gets_new_translation_and_preserves_old(self):
        first = self.prepare()
        before = (first.directory/'Spec.lean').read_bytes()
        self.spec.write_text(self.spec.read_text()+'\n;; changed source identity\n')
        second = self.prepare()
        self.assertNotEqual(first.module, second.module)
        self.assertEqual((first.directory/'Spec.lean').read_bytes(), before)

    def test_check_reconstructs_translation_even_with_repaired_hash(self):
        shared = self.prepare()
        source = shared.directory/'Spec.lean'
        source.write_text(source.read_text()+'\n-- edited cached translation\n')
        path = shared.directory/'identity.json'
        record = json.loads(path.read_text())
        record['generated']['Spec.lean'] = digest(source)
        path.write_text(json.dumps(record))
        with self.assertRaisesRegex(ValueError, 'shared translation.*mismatch'):
            self.prepare(verify=True)

    def test_rejects_symlinked_translation_directory(self):
        other = self.root/'other'
        other.mkdir()
        (self.root/'translated').symlink_to(other, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, 'symlink'):
            self.prepare()

    def test_source_selection_order_has_distinct_identity(self):
        first = self.root/'first.watsup'
        second = self.root/'second.watsup'
        first.write_text('relation First: |- nat hint(input %0)\nrule First/value: |- 1\n')
        second.write_text('relation Second: |- nat hint(input %0)\nrule Second/value: |- 2\n')
        a = prepare_translation([first, second], self.catalog, project=ROOT)
        b = prepare_translation([second, first], self.catalog, project=ROOT)
        self.assertNotEqual(a.module, b.module)

    def test_concurrent_identical_emissions_publish_one_translation(self):
        from scripts.specification import run_checked
        barrier = threading.Barrier(2)
        def translate(*args, **kwargs):
            barrier.wait(timeout=10)
            return run_checked(*args, **kwargs)
        with patch('scripts.specification.run_checked', side_effect=translate):
            with ThreadPoolExecutor(max_workers=2) as workers:
                jobs = [workers.submit(self.prepare) for _ in range(2)]
                results = [job.result(timeout=30) for job in jobs]
        self.assertEqual(results[0], results[1])
