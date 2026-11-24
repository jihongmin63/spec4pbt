"""Re-evaluate the fixed specification with no external adapter process."""
from .codec import CodecError, decode_input
from .coq_codec import constructor_schema
from .compiler import digest
from .dependency import failed_premise
from .engine import BridgeError, BridgeTimeout, run_bridge
from .model import DebugProgram, DebugResult


def debug(program: DebugProgram, input_value, *, timeout=10):
    if not isinstance(program, DebugProgram):
        raise TypeError('debug requires a DebugProgram')
    model = program.model
    if digest(model.source) != model.source_sha256 or digest(model.config) != model.config_sha256:
        return DebugResult('execution_error', {}, reason='fixed source or Property.toml changed')
    if not program.available:
        return DebugResult('unavailable', {}, reason='missing definitions: ' +
                           ', '.join(program.missing))
    try:
        input_value = decode_input(input_value, model.inputs,
                                   constructor_schema(model.type_schema))
    except CodecError as error:
        return DebugResult('execution_error', {}, reason=str(error))
    request = {'input': [input_value[field['name']] for field in model.inputs],
               'pre': model.precondition, 'goal': model.goal}
    try:
        trace = run_bridge('debug', model.source, request, timeout=timeout)
        if trace.get('al_md5') != program.al_md5:
            raise BridgeError('executed AL differs from compiled debug AL')
        status = trace.get('status')
        if status in ('precondition_failed', 'failed'):
            failure = failed_premise(trace)
            stage = 'precondition' if status == 'precondition_failed' else 'goal'
            failure['stage'] = stage
            failure['reason'] = 'specification_' + stage + '_failed'
            trace['failure'] = failure
        if status not in ('passed', 'failed', 'precondition_failed'):
            status = 'execution_error'
        return DebugResult(status, trace)
    except BridgeTimeout as error:
        return DebugResult('unknown', {}, reason=str(error))
    except (BridgeError, OSError, ValueError) as error:
        return DebugResult('execution_error', {}, reason=str(error))
