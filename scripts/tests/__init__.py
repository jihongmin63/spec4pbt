"""Shared locations for maintained repository scripts.tests."""
from scripts.toolchain import PROJECT, SCRATCH_DIRECTORY
from pathlib import Path

ROOT = PROJECT
FIXTURES = Path(__file__).resolve().parent / "fixtures"
ORDERED = Path(__file__).resolve().parent / "ordered"
SCRATCH = ROOT / SCRATCH_DIRECTORY
SCRATCH.mkdir(parents=True, exist_ok=True)
