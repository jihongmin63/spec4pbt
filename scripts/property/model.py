"""Typed property metadata from the pinned SpecTec frontend."""
from dataclasses import dataclass


@dataclass(frozen=True)
class SpecProperty:
    source: str
    source_sha256: str
    config: str
    config_sha256: str
    precondition: str
    goal: str
    inputs: tuple[dict, ...]
    pre_outputs: tuple[str, ...]
    goal_inputs: tuple[str, ...]
    external: tuple[dict, ...]
    definitions: tuple[dict, ...]


class CompileError(ValueError):
    pass


@dataclass(frozen=True)
class ReplayProgram:
    model: SpecProperty
    projection: dict[str, list[int]]
    analysis: dict


@dataclass(frozen=True)
class DebugProgram:
    model: SpecProperty
    available: bool
    missing: tuple[str, ...]
    al_md5: str


@dataclass(frozen=True)
class ReplayResult:
    status: str
    trace: dict
    external_call_count: int
    reason: str = ''


@dataclass(frozen=True)
class DebugResult:
    status: str
    trace: dict
    external_call_count: int = 0
    reason: str = ''
