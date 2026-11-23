#!/usr/bin/env python3
"""Demo implementation: return b=20 for every External(x)."""
import json
import sys


for line in sys.stdin:
    request = json.loads(line)
    print(json.dumps({'status': 'returned', 'fresh_id': request['fresh_id'],
                      'outputs': [{'position': 0,
                                   'value': {'type': 'nat', 'value': '20'}}]}),
          flush=True)
