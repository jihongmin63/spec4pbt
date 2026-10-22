"""Shared locations for maintained repository tests."""
from translator.toolchain import SCRATCH_DIRECTORY
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "tests" / "fixtures"
ORDERED = ROOT / "tests" / "ordered"
SCRATCH = ROOT / SCRATCH_DIRECTORY
SCRATCH.mkdir(parents=True, exist_ok=True)
