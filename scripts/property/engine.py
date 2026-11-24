"""Run one native AL process for one Input and exchange JSON lines."""
import json
import os
import select
import subprocess
import time
from contextvars import ContextVar

from .bridge import ROOT, build_bridge


class BridgeTimeout(TimeoutError):
    pass


class BridgeError(RuntimeError):
    pass


input_deadline = ContextVar('property_input_deadline', default=None)


class JsonLineReader:
    """Read a complete line without blocking beyond an absolute deadline."""

    def __init__(self, stream):
        self.stream = stream
        self.buffer = bytearray()

    def readline(self, deadline):
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise TimeoutError('JSON-lines response timed out')
            end = self.buffer.find(b'\n')
            if end >= 0:
                line = bytes(self.buffer[:end + 1])
                del self.buffer[:end + 1]
                return line.decode('utf-8')
            ready, _, _ = select.select([self.stream], [], [], remaining)
            if not ready:
                raise TimeoutError('JSON-lines response timed out')
            chunk = os.read(self.stream.fileno(), 65536)
            if not chunk:
                line = bytes(self.buffer)
                self.buffer.clear()
                return line.decode('utf-8')
            self.buffer.extend(chunk)


def write_json_line(stream, value, deadline):
    """Write a request without waiting indefinitely for the child to read."""
    data = memoryview((json.dumps(value) + '\n').encode('utf-8'))
    descriptor = stream.fileno()
    was_blocking = os.get_blocking(descriptor)
    os.set_blocking(descriptor, False)
    try:
        while data:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise TimeoutError('JSON-lines request timed out')
            _, ready, _ = select.select([], [stream], [], remaining)
            if not ready:
                raise TimeoutError('JSON-lines request timed out')
            try:
                written = os.write(descriptor, data)
            except BlockingIOError:
                continue
            data = data[written:]
    finally:
        os.set_blocking(descriptor, was_blocking)


def run_bridge(mode, source, request, *, timeout=10, callback=None):
    executable = build_bridge()
    command = ['bash', str(ROOT / 'environment/env.sh'), 'frontend',
               str(executable), mode, str(source)]
    process = subprocess.Popen(command, stdin=subprocess.PIPE,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               text=True, bufsize=1)
    deadline = time.monotonic() + timeout
    reader = JsonLineReader(process.stdout)
    try:
        try:
            write_json_line(process.stdin, request, deadline)
        except TimeoutError as error:
            raise BridgeTimeout('native AL execution timed out') from error
        while True:
            try:
                line = reader.readline(deadline)
            except TimeoutError as error:
                raise BridgeTimeout('native AL execution timed out') from error
            if not line:
                details = process.stderr.read() if process.poll() is not None else ''
                raise BridgeError(details or 'native AL bridge closed its output')
            try:
                response = json.loads(line)
            except json.JSONDecodeError as error:
                raise BridgeError(f'invalid bridge JSON: {line!r}') from error
            if response.get('kind') == 'external_call':
                if callback is None:
                    raise BridgeError('debug attempted an external callback')
                token = input_deadline.set(deadline)
                try:
                    answer = callback(response)
                finally:
                    input_deadline.reset(token)
                if time.monotonic() >= deadline:
                    raise BridgeTimeout('native AL execution timed out')
                try:
                    write_json_line(process.stdin, answer, deadline)
                except TimeoutError as error:
                    raise BridgeTimeout('native AL execution timed out') from error
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
