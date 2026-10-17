"""Check revision/dirty-source boundaries against real disposable Git repos."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from p4bridge.toolchain import resolve_toolchain, bootstrap, UPSTREAM


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args], text=True).strip()


class ToolchainTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.project = Path(self.temp.name) / 'project'
        self.donor = Path(self.temp.name) / 'donor'
        self.upstream = Path(self.temp.name) / 'official'
        for path in [self.project, self.donor, self.upstream]:
            path.mkdir()
            git(path, 'init', '-q')
            git(path, 'config', 'user.name', 'Test')
            git(path, 'config', 'user.email', 'test@example.invalid')
        (self.donor / 'source.ml').write_text('let value = 1\n')
        git(self.donor, 'add', 'source.ml')
        git(self.donor, 'commit', '-qm', 'source')
        self.revision = git(self.donor, 'rev-parse', 'HEAD')
        (self.upstream / 'spec.watsup').write_text('syntax number = int\n')
        git(self.upstream, 'add', 'spec.watsup')
        git(self.upstream, 'commit', '-qm', 'official specification')
        self.upstream_revision = git(self.upstream, 'rev-parse', 'HEAD')
        git(self.project, 'update-index', '--add', '--cacheinfo',
            '160000,' + self.upstream_revision + ',external/p4-spectec')
        (self.project / '.gitmodules').write_text(
            '[submodule "external/p4-spectec"]\n'
            '\tpath = external/p4-spectec\n\turl = ' + UPSTREAM + '\n')
        donor_pin = patch('p4bridge.toolchain.DONOR_REVISION', self.revision, create=True)
        donor_pin.start()
        self.addCleanup(donor_pin.stop)
        binary = self.donor / '_build/default/p4spec/lib/lean-skeleton/main.exe'
        binary.parent.mkdir(parents=True)
        binary.write_text('#!/bin/sh\nexit 0\n')
        binary.chmod(0o755)
        (self.donor / '_build/install/default/lib').mkdir(parents=True)

    def test_clean_pinned_source_resolves_actual_donor_executable(self):
        tool = resolve_toolchain(self.project, self.donor)
        self.assertNotEqual(self.revision, self.upstream_revision)
        self.assertEqual(tool.revision, self.revision)
        self.assertEqual(tool.executable.parent.name, 'lean-skeleton')
        self.assertEqual(tool.root, self.donor)

    def test_environment_donor_resolves_independently_of_official_submodule(self):
        with patch.dict(os.environ, {'P4_SPECTEC_ROOT': str(self.donor)}):
            tool = resolve_toolchain(self.project)
        self.assertEqual(tool.root, self.donor)
        self.assertEqual(tool.identity()['revision'], self.revision)

    def test_official_checkout_cannot_be_used_as_the_lean_donor(self):
        with self.assertRaisesRegex(ValueError, 'revision'):
            resolve_toolchain(self.project, self.upstream, require_built=False)

    def test_changed_tracked_source_is_rejected(self):
        (self.donor / 'source.ml').write_text('let value = 2\n')
        with self.assertRaisesRegex(ValueError, 'tracked|dirty'):
            resolve_toolchain(self.project, self.donor)

    def test_wrong_revision_is_rejected_even_if_binary_exists(self):
        git(self.donor, 'commit', '--allow-empty', '-qm', 'different')
        with self.assertRaisesRegex(ValueError, 'revision'):
            resolve_toolchain(self.project, self.donor)

    def test_non_repository_directory_cannot_inherit_parent_git_identity(self):
        nested = self.donor / 'nested'
        nested.mkdir()
        with self.assertRaisesRegex(ValueError, 'root|checkout'):
            resolve_toolchain(self.project, nested)

    def test_missing_binary_explains_the_donor_build_is_unavailable(self):
        (self.donor / '_build/default/p4spec/lib/lean-skeleton/main.exe').unlink()
        with self.assertRaisesRegex(ValueError, 'build'):
            resolve_toolchain(self.project, self.donor)

    def test_local_bootstrap_initializes_the_pinned_submodule_with_upstream_origin(self):
        destination = bootstrap(self.project, self.upstream)
        self.assertEqual(git(destination, 'rev-parse', 'HEAD'), self.upstream_revision)
        self.assertEqual(git(destination, 'remote', 'get-url', 'origin'), UPSTREAM)
        status = subprocess.check_output(['git', 'submodule', 'status'], cwd=self.project, text=True)
        self.assertTrue(status.startswith(' '), status)
        self.assertEqual(bootstrap(self.project, self.upstream), destination)

    def test_initialized_submodule_replaces_the_previous_fork_origin(self):
        destination = bootstrap(self.project, self.upstream)
        old_url = 'https://example.invalid/previous-fork.git'
        git(destination, 'remote', 'set-url', 'origin', old_url)
        git(self.project, 'config', 'submodule.external/p4-spectec.url', old_url)
        bootstrap(self.project)
        self.assertEqual(git(destination, 'remote', 'get-url', 'origin'), UPSTREAM)
        self.assertEqual(git(self.project, 'config', 'submodule.external/p4-spectec.url'), UPSTREAM)

    def test_default_bootstrap_fetches_the_configured_public_upstream(self):
        # Route the public Git transport to a local remote so this test needs no network.
        with patch.dict(os.environ, {
            'GIT_CONFIG_COUNT': '2',
            'GIT_CONFIG_KEY_0': 'protocol.file.allow',
            'GIT_CONFIG_VALUE_0': 'always',
            'GIT_CONFIG_KEY_1': 'url.' + str(self.upstream) + '.insteadOf',
            'GIT_CONFIG_VALUE_1': UPSTREAM,
        }):
            destination = bootstrap(self.project)
        self.assertEqual(git(destination, 'rev-parse', 'HEAD'), self.upstream_revision)
        self.assertEqual((destination / 'spec.watsup').read_text(), 'syntax number = int\n')
        self.assertEqual(git(destination, 'remote', 'get-url', 'origin'), UPSTREAM)


if __name__ == '__main__':
    unittest.main()
