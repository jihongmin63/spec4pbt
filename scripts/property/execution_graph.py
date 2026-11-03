"""Check nesting and finite descriptions of the pinned recursive call graph.

This parses only the declared source fragments.  It checks observable source
shape and graph coverage, while semantic contracts stay in component_plan's
Lean obligations.  It never treats a source fragment as proof of an ensure.
"""
from __future__ import annotations

from pathlib import Path
import re

from scripts.toolchain import digest
from scripts.property.source_graph import declaration, _flat


def _source(project, anchor):
    if not isinstance(anchor, dict) or set(anchor) != {'path', 'sha256', 'owner', 'fragment'}:
        raise ValueError('execution anchor needs path, sha256, owner, fragment')
    rel = anchor['path']
    if not isinstance(rel, str) or Path(rel).is_absolute():
        raise ValueError('invalid execution source path')
    path = project / rel
    if path.is_symlink() or not path.resolve().is_relative_to(project) or not path.is_file():
        raise ValueError(f'missing execution source: {rel}')
    if not isinstance(anchor['sha256'], str) or digest(path) != anchor['sha256']:
        raise ValueError(f'stale execution source: {rel}')
    if not isinstance(anchor['owner'], str) or not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', anchor['owner']):
        raise ValueError('invalid execution owner')
    fragment = anchor['fragment']
    if not isinstance(fragment, str) or not fragment.strip() or _flat(fragment) not in _flat(declaration(path.read_text(), anchor['owner'])):
        raise ValueError(f'{rel}:{anchor["owner"]} execution fragment is missing')
    return path


def validate(execution, components, project):
    if not isinstance(execution, dict) or set(execution) != {'root', 'frames', 'loops', 'bindings'}:
        raise ValueError('schema 2 needs execution root, frames, loops, bindings')
    if any(not isinstance(execution[key], list) for key in ('frames', 'loops', 'bindings')):
        raise ValueError('execution frames, loops, bindings must be lists')
    frames = {}
    for frame in execution['frames']:
        if not isinstance(frame, dict) or set(frame) != {'id', 'members', 'invocation'}:
            raise ValueError('frame needs id, members, invocation')
        ident = frame['id']
        if not isinstance(ident, str) or not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', ident) or ident in components or ident in frames:
            raise ValueError(f'invalid or duplicate frame {ident}')
        frames[ident] = frame
    root = execution['root']
    if root not in frames:
        raise ValueError('execution root frame is missing')
    parent = {}
    for ident, frame in frames.items():
        members = frame['members']
        if not isinstance(members, list) or not members or any(not isinstance(x, str) for x in members) or len(members) != len(set(members)):
            raise ValueError(f'{ident} needs duplicate-free members')
        if frame['invocation'] is not None:
            _source(project, frame['invocation'])
        for child in members:
            if child not in frames and child not in components:
                raise ValueError(f'{ident} has unknown child {child}')
            if child in parent:
                raise ValueError(f'{child} has two execution parents')
            parent[child] = ident
    if root in parent or set(parent) != (set(frames) | set(components)) - {root}:
        raise ValueError('execution nesting does not cover each component exactly once')
    for ident in frames:
        seen = set()
        current = ident
        while current != root:
            if current in seen or current not in parent:
                raise ValueError(f'cyclic or disconnected execution frame {ident}')
            seen.add(current)
            current = parent[current]
    loops = []
    loop_ids = set()
    for loop in execution['loops']:
        if not isinstance(loop, dict) or set(loop) != {'id', 'component', 'entry', 'recursive', 'base', 'step', 'smaller', 'measure', 'call', 'via'}:
            raise ValueError('loop needs id, component, entry, recursive, base, step, smaller, measure, call, via')
        ident = loop['id']
        if not isinstance(ident, str) or not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', ident) or ident in loop_ids or loop['component'] not in components:
            raise ValueError(f'invalid or duplicate loop {ident}')
        loop_ids.add(ident)
        _source(project, loop['entry'])
        if loop['via'] is not None:
            _source(project, loop['via'])
        path = _source(project, loop['recursive'])
        call = loop['call']
        if not isinstance(call, str) or not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', call) or loop['recursive']['owner'] != call:
            raise ValueError(f'{ident} has an invalid recursive callee')
        body = _flat(declaration(path.read_text(), loop['recursive']['owner']))
        for key in ('base', 'step', 'smaller'):
            if not isinstance(loop[key], str) or _flat(loop[key]) not in body:
                raise ValueError(f'{ident} {key} branch is missing at {path.name}')
        measure = loop['measure']
        if measure not in ('nat', 'list'):
            raise ValueError(f'{ident} has unsupported recursive measure')
        if measure == 'nat' and not re.search(r'\|\s*(?:n|depth)\s*\+\s*1\b', loop['step']):
            raise ValueError(f'{ident} has no predecessor Nat pattern')
        if measure == 'list' and not re.search(r'\|\s*x\s*::\s*xs\b', loop['step']):
            raise ValueError(f'{ident} has no tail List pattern')
        variable = 'xs' if measure == 'list' else ('depth' if 'depth' in loop['step'] else 'n')
        recursive_pattern = (r'\b' + re.escape(call) + r'\s+c\s+env\s+xs\b' if measure == 'list'
                             else r'\b' + re.escape(call) + r'\s+.*?\b' + variable + r'\b(?!\s*\+)')
        if not re.search(recursive_pattern, loop['smaller']):
            raise ValueError(f'{ident} does not recurse on the predecessor')
        loops.append({'id': ident, 'component': loop['component'], 'measure': measure,
                      'call': call, 'via': loop['via'],
                      'source_path': loop['recursive']['path'], 'source_owner': loop['recursive']['owner'],
                      'base': loop['base'], 'step': loop['step'], 'smaller': loop['smaller']})
    bindings = []
    for anchor in execution['bindings']:
        _source(project, anchor)
        bindings.append({'path': anchor['path'], 'owner': anchor['owner'], 'fragment': anchor['fragment']})
    return {'frames': [{'id': ident, 'members': frame['members']} for ident, frame in frames.items()],
            'loops': loops, 'bindings': bindings}
