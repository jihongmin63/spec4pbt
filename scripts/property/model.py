"""Typed property metadata from the pinned SpecTec frontend."""
from dataclasses import dataclass, field


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
    type_schema: dict = field(default_factory=dict)


class CompileError(ValueError):
    def __init__(self, message, *, details=None, code="compile_error"):
        super().__init__(message)
        self.details = details
        self.code = code


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
