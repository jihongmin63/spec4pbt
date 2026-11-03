"""Conservative, syntactic correspondence between a plan and pinned Lean calls.

This is deliberately a source-shape check, not a proof about the generator's
support or its four-field contracts.  A site names the enclosing definition,
the exact call/definition fragment, and the projections represented by the
typed planning values.  The full file digest is checked by component_plan.
"""
from __future__ import annotations

import re
from pathlib import Path

from scripts.toolchain import digest


DECL = re.compile(r'(?m)^(?:def|abbrev|theorem|structure|inductive)\s+([A-Za-z][A-Za-z0-9_]*)\b')


def _flat(text):
    return ' '.join(text.split())


def declaration(source, symbol):
    matches = list(DECL.finditer(source))
    for index, match in enumerate(matches):
        if match.group(1) == symbol:
            return source[match.start():matches[index + 1].start() if index + 1 < len(matches) else len(source)]
    raise ValueError(f'source declaration {symbol} is missing')


def check_site(path, site, inputs, outputs, project):
    if not isinstance(site, dict) or set(site) != {'owner', 'kind', 'fragment', 'uses', 'conditions', 'projections', 'result'}:
        raise ValueError('source site needs owner, kind, fragment, uses, conditions, projections, result')
    if site['kind'] not in ('call', 'definition', 'expression'):
        raise ValueError('unsupported source site kind')
    if not isinstance(site['owner'], str) or not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', site['owner']):
        raise ValueError('invalid source site owner')
    fragment = site['fragment']
    if not isinstance(fragment, str) or not fragment.strip():
        raise ValueError('empty source site fragment')
    if not isinstance(site['uses'], dict) or not isinstance(site['conditions'], list) or any(not isinstance(x, str) for x in site['conditions']) or len(site['conditions']) != len(set(site['conditions'])) or set(site['uses']) & set(site['conditions']) or set(site['uses']) | set(site['conditions']) != set(inputs):
        raise ValueError(f'{site["owner"]} source uses/conditions do not account for component inputs')
    if not isinstance(site['projections'], dict) or set(site['projections']) != set(outputs):
        raise ValueError(f'{site["owner"]} source projections do not match component outputs')
    body = declaration(path.read_text(), site['owner'])
    flat = _flat(body)
    needle = _flat(fragment)
    if needle not in flat:
        raise ValueError(f'{path.name}:{site["owner"]} source fragment is missing or stale: {needle}')
    if site['kind'] == 'call' and not re.search(r'\blet\s+[A-Za-z][A-Za-z0-9_]*\s*←\s*' + re.escape(needle), flat):
        raise ValueError(f'{path.name}:{site["owner"]} is not the asserted bound call')
    if site['kind'] in ('definition', 'expression') and len(outputs) != 1:
        raise ValueError(f'{path.name}:{site["owner"]} pure expression must have one projected output')
    fields = None
    result = site['result']
    if result is not None:
        if site['kind'] != 'call' or not isinstance(result, dict) or set(result) != {'path', 'sha256', 'structure'}:
            raise ValueError(f'{path.name}:{site["owner"]} has invalid result structure reference')
        rel = result['path']
        if not isinstance(rel, str) or Path(rel).is_absolute():
            raise ValueError('invalid result structure path')
        target = project / rel
        if target.is_symlink() or not target.resolve().is_relative_to(project) or not target.is_file() or digest(target) != result['sha256']:
            raise ValueError(f'stale or missing source result structure: {rel}')
        callee = re.search(r'\b(Constructive[A-Za-z0-9_]+)\.(?:generate|fromEmpty)\b', needle)
        if callee is None or target.stem != callee.group(1):
            raise ValueError(f'{path.name}:{site["owner"]} result structure is not from the bound callee')
        structure = result['structure']
        if not isinstance(structure, str) or not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', structure):
            raise ValueError('invalid result structure name')
        source = declaration(target.read_text(), structure)
        if not source.startswith('structure '):
            raise ValueError(f'{rel}:{structure} is not a structure')
        fields = set(re.findall(r'(?m)^\s{2}([A-Za-z][A-Za-z0-9_]*)\s*:', source))
    for value, expression in site['uses'].items():
        if not isinstance(expression, str) or not expression.strip() or _flat(expression) not in needle:
            raise ValueError(f'{path.name}:{site["owner"]} input {value} is absent at the source site')
    for value, expression in site['projections'].items():
        if not isinstance(expression, str) or not expression.strip():
            raise ValueError(f'{path.name}:{site["owner"]} output {value} has no source projection')
        if site['kind'] == 'call':
            binding = re.search(r'\blet\s+([A-Za-z][A-Za-z0-9_]*)\s*←\s*' + re.escape(needle), flat).group(1)
            if not re.fullmatch(re.escape(binding) + r'(?:\.[A-Za-z][A-Za-z0-9_]*)*', expression):
                raise ValueError(f'{path.name}:{site["owner"]} output {value} is not a projection of {binding}')
            parts = expression.split('.')[1:]
            if fields is not None and (not parts or parts[0] not in fields):
                raise ValueError(f'{path.name}:{site["owner"]} output {value} is not a declared result field')
            if fields is None and parts != ['val']:
                raise ValueError(f'{path.name}:{site["owner"]} output {value} needs a result structure')
        elif _flat(expression) not in flat:
            raise ValueError(f'{path.name}:{site["owner"]} output {value} projection is absent')
    return {'owner': site['owner'], 'kind': site['kind'], 'fragment': needle}
