#!/usr/bin/env python3
"""Reference implementation of the observed b output."""
import json
import sys

for line in sys.stdin:
    request = json.loads(line)
    print(json.dumps({
        'status': 'returned',
        'fresh_id': request['fresh_id'],
        'outputs': [{'position': 0, 'value': {'type': 'nat', 'value': '10'}}],
    }), flush=True)
