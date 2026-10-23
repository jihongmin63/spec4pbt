"""Exercise local translator freshness and official submodule isolation."""
import os
import json
from types import SimpleNamespace
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from translator import toolchain
from translator.toolchain import build, resolve_toolchain, metadata_executable, bootstrap, UPSTREAM


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args], text=True).strip()


class ToolchainTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.project = Path(self.temp.name) / 'project'
        self.upstream = Path(self.temp.name) / 'official'
        for path in [self.project, self.upstream]:
            path.mkdir()
            git(path, 'init', '-q')
            git(path, 'config', 'user.name', 'Test')
            git(path, 'config', 'user.email', 'test@example.invalid')
        self.original_pass = 'let algo_spec = Algo.algo_spec\n'
        source = self.upstream / 'p4spec/lib/pass/pass.ml'
        source.parent.mkdir(parents=True)
        source.write_text(self.original_pass)
        (self.upstream / 'spec.watsup').write_text('syntax number = int\n')
        git(self.upstream, 'add', '.')
        git(self.upstream, 'commit', '-qm', 'official specification')
        self.upstream_revision = git(self.upstream, 'rev-parse', 'HEAD')
        git(self.project, 'update-index', '--add', '--cacheinfo',
            '160000,' + self.upstream_revision + ',p4-spectec')
        (self.project / '.gitmodules').write_text(
            '[submodule "p4-spectec"]\n'
            '\tpath = p4-spectec\n\turl = ' + UPSTREAM + '\n')
        self.backend = self.project / 'translator/src'
        self.backend.mkdir(parents=True)
        (self.backend / 'main.ml').write_text('let () = print_endline "translation"\n')
        (self.backend / 'dune').write_text('(executable (name main))\n')
        patches = self.project / 'translator/patches'
        patches.mkdir()
        self.compatibility_patch = patches / 'algo-defs.patch'
        self.compatibility_patch.write_text(
            'diff --git a/p4spec/lib/pass/pass.ml b/p4spec/lib/pass/pass.ml\n'
            '--- a/p4spec/lib/pass/pass.ml\n'
            '+++ b/p4spec/lib/pass/pass.ml\n'
            '@@ -1 +1,2 @@\n'
            ' let algo_spec = Algo.algo_spec\n'
            '+let algo_defs = Algo.algo_defs\n')
        bridge = self.project / 'translator/bridge'
        bridge.mkdir()
        (bridge / 'property_cli.ml').write_text('let () = ()\n')
        (bridge / 'property_al.ml').write_text('let () = ()\n')
        (bridge / 'property_exec.ml').write_text('let () = ()\n')
        (bridge / 'property_document.ml').write_text('let () = ()\n')
        (bridge / 'metadata.ml').write_text('let () = print_endline "metadata"\n')
        (self.project / 'translator/toolchain.py').write_text(Path(toolchain.__file__).read_text())
        self.real_command = toolchain.command
        self.compiler = patch('translator.toolchain.command', side_effect=self.command)
        self.compiler.start()
        self.addCleanup(self.compiler.stop)
        self.on_compile = None

    def command(self, args, cwd, **kwargs):
        # Keep archive/patch/submodule operations real; stub only the expensive
        # OCaml compiler. Full translator tests exercise the actual compiler.
        if str(args[0]) != 'opam':
            return self.real_command(args, cwd, **kwargs)
        if list(args[1:]) == ['switch', 'show']:
            return 'active-test-switch'
        self.assertIn('dune', args)
        self.assertIn('build', args)
        overlay = Path(cwd)
        for target in [
            'p4spec/lib/lean-skeleton/main.exe',
            'p4spec/lib/spec4pbt-metadata/metadata.exe',
            'p4spec/lib/spec4pbt-property/property_cli.exe',
            'p4spec/lib/spec4pbt-property/property_exec.exe',
        ]:
            executable = overlay / '_build/default' / target
            executable.parent.mkdir(parents=True, exist_ok=True)
            executable.write_text('#!/bin/sh\nprintf "local compiler output\\n"\n')
            executable.chmod(0o755)
        if self.on_compile is not None:
            self.on_compile()
        return ''

    def built(self, *, switch='test-switch'):
        bootstrap(self.project, self.upstream)
        return build(self.project, switch=switch)

    def test_build_uses_local_sources_without_changing_official_submodule(self):
        tool = self.built()
        official = self.project / 'p4-spectec'
        self.assertEqual(tool.root, self.project / 'out/translator/p4-spectec')
        self.assertEqual(tool.revision, self.upstream_revision)
        self.assertEqual((tool.root / 'p4spec/lib/lean-skeleton/main.ml').read_bytes(),
                         (self.backend / 'main.ml').read_bytes())
        self.assertIn('let algo_defs', (tool.root / 'p4spec/lib/pass/pass.ml').read_text())
        self.assertEqual((official / 'p4spec/lib/pass/pass.ml').read_text(), self.original_pass)
        self.assertEqual(git(official, 'status', '--porcelain'), '')
        self.assertTrue(metadata_executable(self.project, tool).is_file())
        identity = tool.identity()
        self.assertEqual(identity['upstream_revision'], self.upstream_revision)
        self.assertEqual(identity['switch'], 'test-switch')
        self.assertNotIn('donor_root', identity)

    def test_external_docker_environment_is_ignored(self):
        tool = self.built()
        with patch.dict(os.environ, {'P4_SPECTEC_ROOT': '/does/not/exist'}):
            self.assertEqual(resolve_toolchain(self.project).executable, tool.executable)

    def test_backend_patch_applies_to_copy_and_is_fingerprinted(self):
        backend_patch = self.project / 'translator/patches/backend.patch'
        backend_patch.write_text(
            '--- a/p4spec/lib/lean-skeleton/main.ml\n'
            '+++ b/p4spec/lib/lean-skeleton/main.ml\n'
            '@@ -1 +1 @@\n'
            '-let () = print_endline "translation"\n'
            '+let () = print_endline "singleton translation"\n')
        tool = self.built()
        self.assertEqual((tool.root / 'p4spec/lib/lean-skeleton/main.ml').read_text(),
                         'let () = print_endline "singleton translation"\n')
        self.assertEqual((self.backend / 'main.ml').read_text(),
                         'let () = print_endline "translation"\n')
        self.assertEqual(git(self.project / 'p4-spectec', 'status', '--porcelain'), '')
        backend_patch.write_text(backend_patch.read_text() + '\n')
        with self.assertRaisesRegex(ValueError, 'stale'):
            tool.identity()

    def test_missing_local_build_does_not_fall_back_to_external_donor(self):
        bootstrap(self.project, self.upstream)
        with patch.dict(os.environ, {'P4_SPECTEC_ROOT': str(self.upstream)}):
            with self.assertRaisesRegex(ValueError, 'translator.toolchain build'):
                resolve_toolchain(self.project)

    def test_default_build_uses_active_switch_and_resolution_remembers_it(self):
        tool = self.built(switch=None)
        self.assertEqual(tool.switch, 'active-test-switch')
        self.assertEqual(resolve_toolchain(self.project).switch, tool.switch)
        with self.assertRaisesRegex(ValueError, 'stale|switch'):
            resolve_toolchain(self.project, switch='different-switch')

    def test_backend_source_change_requires_rebuild(self):
        tool = self.built()
        (self.backend / 'main.ml').write_text('let () = ()\n')
        with self.assertRaisesRegex(ValueError, 'stale'):
            tool.identity()

    def test_patch_change_requires_rebuild(self):
        self.built()
        with self.compatibility_patch.open('a') as stream:
            stream.write('\n')
        with self.assertRaisesRegex(ValueError, 'stale'):
            resolve_toolchain(self.project)

    def test_helper_and_build_recipe_changes_require_rebuild(self):
        for path in ['translator/bridge/metadata.ml', 'translator/toolchain.py',
                     'translator/bridge/property_al.ml', 'translator/bridge/property_exec.ml',
                     'translator/bridge/property_document.ml']:
            with self.subTest(path=path):
                tool = self.built()
                file = self.project / path
                original = file.read_bytes()
                file.write_bytes(original + b'\n')
                with self.assertRaisesRegex(ValueError, 'stale'):
                    metadata_executable(self.project, tool)
                file.write_bytes(original)

    def test_binary_changes_require_rebuild(self):
        for artifact in ['translator', 'metadata', 'property_exec']:
            with self.subTest(artifact=artifact):
                tool = self.built()
                binary = (tool.executable if artifact == 'translator' else
                          metadata_executable(self.project, tool) if artifact == 'metadata' else
                          tool.root / toolchain.PROPERTY_RUN_EXECUTABLE)
                binary.write_text('#!/bin/sh\nexit 42\n')
                with self.assertRaisesRegex(ValueError, 'stale'):
                    resolve_toolchain(self.project)

    def test_dirty_official_source_is_rejected(self):
        tool = self.built()
        (self.project / 'p4-spectec/spec.watsup').write_text('changed\n')
        with self.assertRaisesRegex(ValueError, 'dirty|tracked'):
            tool.identity()

    def test_changed_upstream_pin_is_rejected(self):
        self.built()
        official = self.project / 'p4-spectec'
        git(official, '-c', 'user.name=Test', '-c', 'user.email=test@example.invalid',
            'commit', '--allow-empty', '-qm', 'new official revision')
        revision = git(official, 'rev-parse', 'HEAD')
        git(self.project, 'update-index', '--cacheinfo', '160000,' + revision + ',p4-spectec')
        with self.assertRaisesRegex(ValueError, 'stale'):
            resolve_toolchain(self.project)

    def test_rebuild_discards_manual_overlay_changes(self):
        tool = self.built()
        copied = tool.root / 'p4spec/lib/lean-skeleton/main.ml'
        copied.write_text('corrupted copied source\n')
        build(self.project, switch='test-switch')
        self.assertEqual(copied.read_bytes(), (self.backend / 'main.ml').read_bytes())

    def test_failed_build_invalidates_previous_success(self):
        self.built()
        def fail():
            raise ValueError('compiler failed')
        self.on_compile = fail
        with self.assertRaisesRegex(ValueError, 'compiler failed'):
            build(self.project, switch='test-switch')
        with self.assertRaisesRegex(ValueError, 'translator.toolchain build'):
            resolve_toolchain(self.project)

    def test_sources_changed_during_build_are_not_certified(self):
        bootstrap(self.project, self.upstream)
        self.on_compile = lambda: (self.backend / 'main.ml').write_text('changed while compiling\n')
        with self.assertRaisesRegex(ValueError, 'changed during'):
            build(self.project, switch='test-switch')
        with self.assertRaisesRegex(ValueError, 'translator.toolchain build'):
            resolve_toolchain(self.project)

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
        git(self.project, 'config', 'submodule.p4-spectec.url', old_url)
        bootstrap(self.project)
        self.assertEqual(git(destination, 'remote', 'get-url', 'origin'), UPSTREAM)
        self.assertEqual(git(self.project, 'config', 'submodule.p4-spectec.url'), UPSTREAM)

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


class SourceIdentityTests(unittest.TestCase):
    def test_directory_provenance_includes_linked_sources_and_skips_include(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            sources = root / 'sources'
            sources.mkdir()
            actual = root / 'actual'
            actual.mkdir()
            (sources / 'anchor.watsup').write_text('')
            target = actual / 'spec.watsup'
            target.write_text('syntax number = int')
            (sources / 'linked').symlink_to(actual, target_is_directory=True)
            (sources / 'include').mkdir()
            (sources / 'include/ignored.watsup').write_text('ignored')
            before = toolchain.source_identity([sources])
            self.assertEqual(set(before),
                {str(sources / 'anchor.watsup'), str(sources / 'linked/spec.watsup')})
            target.write_text('changed semantics')
            self.assertNotEqual(toolchain.source_identity([sources]), before)

    def test_directory_cycle_is_rejected_before_translation(self):
        with tempfile.TemporaryDirectory() as directory:
            sources = Path(directory)
            (sources / 'loop').symlink_to(sources, target_is_directory=True)
            with self.assertRaisesRegex(ValueError, 'cycle'):
                toolchain.source_identity([sources])


class TranslationCommandTests(unittest.TestCase):
    def test_native_arguments_and_exit_status_are_preserved(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            record = root / 'arguments.json'
            executable = root / 'translator'
            executable.write_text('#!/usr/bin/env python3\nimport json,sys\n'
                + f'open({str(record)!r}, "w").write(json.dumps(sys.argv[1:]))\n'
                + 'raise SystemExit(7)\n')
            executable.chmod(0o755)
            with patch.object(toolchain, 'resolve_toolchain',
                              return_value=SimpleNamespace(executable=executable)):
                code = toolchain.main(['translate', '--emit-modules', 'folder with spaces', '--keep-going'])
            self.assertEqual(code, 7)
            self.assertEqual(json.loads(record.read_text()),
                             ['--emit-modules', 'folder with spaces', '--keep-going'])


if __name__ == '__main__':
    unittest.main()
