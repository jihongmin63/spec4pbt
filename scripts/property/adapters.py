"""One JSON-lines adapter session per Input, with strict typed responses."""
import json
import subprocess
import time

from .codec import CodecError, decode_value, encode_value
from .coq_codec import constructor_schema
from .engine import JsonLineReader, input_deadline, write_json_line


class AdapterProtocolError(RuntimeError):
    pass


class AdapterTimeout(TimeoutError):
    pass


class AdapterSession:
    def __init__(self, program, commands, *, timeout=5):
        self.program = program
        self.commands = commands
        self.timeout = timeout
        self.processes = []
        self.call_count = 0
        self.failed = False
        self.deadline = None
        self.contracts = {item['relation']: item for item in program.model.external}
        self.definitions = {item['name']: item for item in program.model.definitions}
        self.constructors = constructor_schema(program.model.type_schema)

    def __enter__(self):
        self.deadline = time.monotonic() + self.timeout
        return self

    def __exit__(self, *_):
        self.close()

    def close(self):
        for process in self.processes:
            if process.poll() is None:
                process.terminate()
                try:
                    process.wait(timeout=1)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.wait()
            for stream in (process.stdin, process.stdout, process.stderr):
                if stream:
                    stream.close()
        self.processes.clear()

    def _process(self, name):
        command = self.commands.get(name)
        if not command:
            raise AdapterProtocolError(f'no adapter command for {name}')
        process = subprocess.Popen(
            command, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, text=True, bufsize=1)
        self.processes.append(process)
        return process

    def call(self, relation, inputs, fresh_id):
        if self.failed:
            raise AdapterProtocolError('adapter session stopped after an error')
        if self.deadline is None:
            self.deadline = time.monotonic() + self.timeout
        deadline = self.deadline
        native_deadline = input_deadline.get()
        if native_deadline is not None:
            deadline = min(deadline, native_deadline)
        if time.monotonic() >= deadline:
            self.failed = True
            raise AdapterTimeout(f'{relation}: input timed out')
        if type(fresh_id) is not int or fresh_id < 0:
            raise AdapterProtocolError('request fresh_id must be a natural number')
        contract = self.contracts.get(relation)
        if contract is None:
            raise AdapterProtocolError(f'undeclared external relation: {relation}')
        definition = self.definitions[relation]
        if len(inputs) != len(definition['input_types']):
            raise AdapterProtocolError(f'{relation}: input arity mismatch')
        try:
            inputs = [encode_value(decode_value(value, typ, self.constructors)) for value, typ
                      in zip(inputs, definition['input_types'])]
        except CodecError as error:
            raise AdapterProtocolError(str(error)) from error
        process = self._process(contract['adapter'])
        request = {'relation': relation, 'input': inputs,
                   'fresh_id': fresh_id,
                   'observed_outputs': contract['observed_outputs']}
        try:
            try:
                write_json_line(process.stdin, request, deadline)
                self.call_count += 1
                line = JsonLineReader(process.stdout).readline(deadline)
            except TimeoutError as error:
                self.failed = True
                raise AdapterTimeout(f'{relation}: adapter timed out') from error
            if not line:
                raise AdapterProtocolError(f'{relation}: adapter exited before response')
            response = json.loads(line)
            return self._validate(relation, response, contract, definition)
        except (OSError, ValueError, AdapterProtocolError):
            self.failed = True
            raise

    def _validate(self, relation, response, contract, definition):
        if not isinstance(response, dict) or response.get('status') not in ('returned', 'no_match'):
            raise AdapterProtocolError(f'{relation}: invalid status')
        fresh = response.get('fresh_id')
        if type(fresh) is not int or fresh < 0:
            raise AdapterProtocolError(f'{relation}: fresh_id must be a natural number')
        if response['status'] == 'no_match':
            if set(response) != {'status', 'fresh_id'}:
                raise AdapterProtocolError(f'{relation}: no_match cannot contain outputs')
            return {'status': 'no_match', 'fresh_id': fresh}
        if set(response) != {'status', 'fresh_id', 'outputs'} or not isinstance(response['outputs'], list):
            raise AdapterProtocolError(f'{relation}: returned response requires outputs')
        positions = contract['observed_outputs']
        found = [item.get('position') for item in response['outputs']
                 if isinstance(item, dict)]
        if (any(type(position) is not int for position in found) or
                found != positions or len(found) != len(response['outputs'])):
            raise AdapterProtocolError(f'{relation}: output positions differ from contract')
        outputs = []
        for item in response['outputs']:
            if set(item) != {'position', 'value'}:
                raise AdapterProtocolError(f'{relation}: invalid output item')
            position = item['position']
            try:
                value = decode_value(item['value'], definition['output_types'][position],
                                     self.constructors)
            except (CodecError, IndexError) as error:
                raise AdapterProtocolError(f'{relation}: {error}') from error
            outputs.append({'position': position, 'value': encode_value(value)})
        return {'status': 'returned', 'fresh_id': fresh, 'outputs': outputs}
