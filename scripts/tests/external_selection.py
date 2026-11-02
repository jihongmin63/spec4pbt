"""Build explicit selection fixtures for tests of pre-existing profile behavior."""
import json
from pathlib import Path
import tomllib


def select_all(config_path):
    path = Path(config_path)
    with path.open('rb') as source:
        config = tomllib.load(source)
    lines = ['schema_version = 1']
    profiles = config.get('observations', [])
    if not profiles:
        lines.append('external = []')
    for profile in profiles:
        lines.extend(['[[external]]', 'id = ' + json.dumps(profile['id']),
                      'observe = ' + json.dumps(profile['observe'])])
    selection = path.with_name(path.stem + '-external.toml')
    selection.write_text('\n'.join(lines) + '\n')
    return selection
