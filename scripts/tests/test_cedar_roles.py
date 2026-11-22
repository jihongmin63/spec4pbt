"""Role harness regressions; these never call an experimental model role."""

import json
from pathlib import Path
import shutil
import subprocess
import time
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
from cedar import roles


class UsageTests(unittest.TestCase):
    def test_completed_turns_are_summed_without_double_counting_subfields(self):
        events = [
            {"type": "turn.completed", "usage": {"input_tokens": 100, "output_tokens": 50,
                                                  "cached_input_tokens": 40, "reasoning_output_tokens": 10}},
            {"type": "thread.token_usage", "usage": {"input_tokens": 1000, "output_tokens": 1000}},
            {"type": "turn.completed", "usage": {"input_tokens": 20, "output_tokens": 30,
                                                  "cached_input_tokens": 5, "reasoning_output_tokens": 2}},
        ]
        self.assertEqual(roles.parse_usage(events), {
            "status": "available", "input_tokens": 120, "output_tokens": 80,
            "cached_input_tokens": 45, "reasoning_output_tokens": 12})

    def test_missing_usage_is_unavailable_and_uncalled_prover_is_not_run(self):
        self.assertEqual(roles.parse_usage([])["status"], "unavailable")
        self.assertIsNone(roles.parse_usage([{"type": "turn.completed"}])["input_tokens"])
        self.assertIsNone(roles.parse_usage([{"type": "turn.completed", "usage": {
            "input_tokens": 7, "output_tokens": 3}}])["cached_input_tokens"])
        self.assertEqual(roles.not_run_cost()["usage"]["status"], "not_run")
        self.assertIsNone(roles.not_run_cost()["wall_seconds"])
        partial = [{"type": "turn.started"}, {"type": "turn.completed", "usage": {
            "input_tokens": 10, "output_tokens": 2}}, {"type": "turn.started"}]
        self.assertEqual(roles.parse_usage(partial)["status"], "unavailable")
        self.assertIsNone(roles.parse_usage(partial)["input_tokens"])
        self.assertEqual(roles.parse_usage(partial[:2], call_complete=False)["status"], "unavailable")


class PreparationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="cedar-role-test-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.source = self.root / "fixed-source"
        self.source.mkdir()
        (self.source / "AGENTS.md").write_text("fixed source\n")
        (self.source / "Spec.v").write_text("Definition specification := True.\n")
        (self.source / "Original.v").write_text("Definition Input := nat.\n")
        (self.source / "Candidate.v").write_text("Inductive predicate : nat -> Prop := one : predicate 1.\n")
        (self.source / "environment").mkdir()
        shutil.copyfile(ROOT / "environment/env.sh", self.source / "environment/env.sh")
        self.inputs = {"specification/cedar/Spec.v": self.source / "Spec.v",
                       "property/Original.v": self.source / "Original.v"}

    def test_fresh_workspaces_and_private_manifest(self):
        first = roles.prepare_role("reformulator", self.root / "run", self.inputs,
                                   {"baseline_valid_ratio": 0.125})
        second = roles.prepare_role("reformulator", self.root / "run", self.inputs)
        self.assertNotEqual(first["workspace"], second["workspace"])
        self.assertEqual((Path(first["workspace"]) / "property/Original.v").read_text(),
                         (self.source / "Original.v").read_text())
        manifest = json.loads((Path(first["workspace"]).parent / "manifest.json").read_text())
        self.assertNotIn("baseline_valid_ratio", json.dumps(manifest))
        self.assertFalse((Path(first["workspace"]) / "Candidate.v").exists())

    def test_role_bundle_rejects_private_logs_and_symlinks(self):
        bad = self.source / "events.jsonl"
        bad.write_text("private")
        with self.assertRaises(roles.RoleError):
            roles.prepare_role("reformulator", self.root / "run",
                               {**self.inputs, "events.jsonl": bad})
        link = self.source / "Linked.v"
        link.symlink_to(self.source / "Original.v")
        with self.assertRaises(roles.RoleError):
            roles.prepare_role("reformulator", self.root / "run",
                               {**self.inputs, "Linked.v": link})

    def test_real_landlock_probe_blocks_sibling_and_proc_root_paths(self):
        other_run = self.root / "other-run" / "private-evidence"
        other_run.mkdir(parents=True)
        secret = other_run / "events.txt"
        secret.write_text("private")
        result = roles.run_role("prover", self.source, self.root / "run",
                                {**self.inputs, "Candidate.v": self.source / "Candidate.v"},
                                {"theorem_type": "forall x : nat, True"},
                                forbidden_paths=[secret],
                                switch=Path("/workspace/spec4pbt/_opam-testing-theorems"),
                                probe_only=True)
        self.assertEqual(result["status"], "probe_passed")
        checks = result["probe"]["results"]
        self.assertTrue(all(item["blocked"] for item in checks[:-1]))
        self.assertEqual({item["kind"] for item in checks},
                         {"direct", "proc-root", "write", "allowed-write"})
        self.assertFalse(checks[-1]["blocked"])
        self.assertTrue((Path(result["manifest"]["workspace"]) / "environment/env.sh").is_file())

    def test_inventory_catches_any_rogue_file_or_symlink(self):
        manifest = roles.prepare_role("prover", self.root / "run",
                                      {**self.inputs, "Candidate.v": self.source / "Candidate.v"})
        workspace = Path(manifest["workspace"])
        baseline = roles._source_inventory(workspace)
        (workspace / "rogue.py").write_text("pass\n")
        (workspace / "linked-source").symlink_to(self.source, target_is_directory=True)
        current = roles._source_inventory(workspace)
        self.assertIn("rogue.py", current.keys() - baseline.keys())
        self.assertIn("linked-source", current.keys() - baseline.keys())

    def test_fixed_env_wrapper_compiles_quickchick_under_restriction(self):
        switch = Path("/workspace/spec4pbt/_opam-testing-theorems")
        workspace = self.root / "inspector-workspace"
        workspace.mkdir()
        # A fresh inspector has a private HOME unrelated to installed Opam.
        with patch.object(Path, "home", return_value=workspace):
            roles._setup_coq_runtime(workspace, self.source, switch)
        (workspace / "Probe.v").write_text(
            "From QuickChick Require Import QuickChick.\n"
            "Theorem probe : True. Proof. exact I. Qed.\n")
        env = {"PATH": "/usr/bin:/bin", "HOME": str(workspace),
               "TMPDIR": str(workspace), "OPAMROOT": str(workspace / ".opam")}
        result = subprocess.run(["bash", "environment/env.sh", "coqc", "Probe.v"],
                                cwd=workspace, env=env, capture_output=True, text=True,
                                timeout=30, preexec_fn=lambda: roles._restrict(
                                    roles.runtime_read_paths(switch) + [workspace], workspace))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertTrue((workspace / "Probe.vo").exists())
        self.assertFalse((workspace / ".codex/auth.json").exists())

    def test_real_check_script_uses_local_scratch_switch_under_restriction(self):
        switch = Path("/workspace/spec4pbt/_opam-testing-theorems")
        workspace = self.root / "check-workspace"
        workspace.mkdir()
        roles._setup_coq_runtime(workspace, self.source, switch)
        (workspace / "scripts").mkdir()
        shutil.copyfile(ROOT / "scripts/check.py", workspace / "scripts/check.py")
        spec = workspace / "specification/cedar/Spec.v"
        spec.parent.mkdir(parents=True)
        spec.write_text("Definition specification := True.\n")
        prop = workspace / "property"
        candidate = prop / "candidates/v001"
        candidate.mkdir(parents=True)
        (prop / "Original.v").write_text(
            "Definition Input := nat.\nDefinition predicate (_ : Input) : Prop := True.\n")
        (candidate / "Candidate.v").write_text(
            "Require Import Property.Original.\nDefinition predicate := Original.predicate.\n")
        (candidate / "Equivalence.v").write_text(
            "Require Import Property.Original Property.candidates.v001.Candidate.\n"
            "Theorem equivalent : forall x : Original.Input, Original.predicate x <-> "
            "Candidate.predicate x.\nProof. intro x; split; trivial. Qed.\n")
        env = {"PATH": "/usr/bin:/bin", "HOME": str(workspace),
               "TMPDIR": str(workspace), "OPAMROOT": str(workspace / ".opam")}
        result = subprocess.run([sys.executable, "scripts/check.py", "property"],
                                cwd=workspace, env=env, capture_output=True, text=True,
                                timeout=120, preexec_fn=lambda: roles._restrict(
                                    roles.runtime_read_paths(switch) + [workspace], workspace))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        reports = list((prop / ".runs").glob("*/result.json"))
        self.assertEqual(len(reports), 1)
        self.assertEqual(json.loads(reports[0].read_text())["status"], "passed")

    @unittest.skipUnless(shutil.which("codex"),
                         "codex CLI is not installed; model roles cannot run on this host")
    def test_codex_command_host_can_start_under_runtime_restriction(self):
        host = Path(shutil.which("codex")).resolve().with_name("codex-code-mode-host")
        self.assertTrue(host.is_file())
        workspace = self.root / "command-host-workspace"
        workspace.mkdir()
        result = subprocess.run([str(host), "--help"], cwd=workspace,
                                capture_output=True, text=True, timeout=15,
                                preexec_fn=lambda: roles._restrict(
                                    roles.runtime_read_paths() + [workspace], workspace))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("codex-code-mode-host", result.stdout)

    def test_cli_timeout_kills_descendant_process_group(self):
        workspace = self.root / "timeout-workspace"
        workspace.mkdir()
        evidence = self.root / "timeout-evidence"
        evidence.mkdir()
        marker = workspace / "descendant-survived"
        child = f"import time; from pathlib import Path; time.sleep(0.4); Path({str(marker)!r}).write_text('bad')"
        parent = f"import subprocess,sys,time; subprocess.Popen([sys.executable,'-c',{child!r}]); time.sleep(30)"
        returncode, status = roles._run_cli_group(
            [sys.executable, "-c", parent], "", workspace, evidence,
            {"PATH": "/usr/bin:/bin", "HOME": str(workspace)},
            roles.runtime_read_paths() + [workspace], 0.05)
        self.assertEqual(status, "timeout")
        self.assertLess(returncode, 0)
        time.sleep(0.5)
        self.assertFalse(marker.exists())


if __name__ == "__main__":
    unittest.main()
