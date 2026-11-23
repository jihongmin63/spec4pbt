"""Run one native AL process for one Input and exchange JSON lines."""
import json
import select
import subprocess
import time

from .bridge import ROOT, build_bridge


class BridgeTimeout(TimeoutError):
    pass


class BridgeError(RuntimeError):
    pass


def run_bridge(mode, source, request, *, timeout=10, callback=None):
    executable = build_bridge()
    command = ['bash', str(ROOT / 'environment/env.sh'), 'frontend',
               str(executable), mode, str(source)]
    process = subprocess.Popen(command, stdin=subprocess.PIPE,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               text=True, bufsize=1)
    deadline = time.monotonic() + timeout
    try:
        process.stdin.write(json.dumps(request) + '\n')
        process.stdin.flush()
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise BridgeTimeout('native AL execution timed out')
            ready, _, _ = select.select([process.stdout], [], [], remaining)
            if not ready:
                raise BridgeTimeout('native AL execution timed out')
            line = process.stdout.readline()
            if not line:
                raise BridgeError(process.stderr.read() or 'native AL bridge exited')
            try:
                response = json.loads(line)
            except json.JSONDecodeError as error:
                raise BridgeError(f'invalid bridge JSON: {line!r}') from error
            if response.get('kind') == 'external_call':
                if callback is None:
                    raise BridgeError('debug attempted an external callback')
                answer = callback(response)
                process.stdin.write(json.dumps(answer) + '\n')
                process.stdin.flush()
                continue
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise BridgeTimeout('native AL execution timed out')
            try:
                code = process.wait(timeout=remaining)
            except subprocess.TimeoutExpired as error:
                raise BridgeTimeout('native AL execution timed out') from error
            if code:
                raise BridgeError(process.stderr.read() or f'bridge exited {code}')
            return response
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()
        for stream in (process.stdin, process.stdout, process.stderr):
            if stream:
                stream.close()
