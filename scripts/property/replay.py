"""Execute the original property against actual external observations."""
from .adapters import AdapterProtocolError, AdapterSession, AdapterTimeout
from .codec import CodecError, decode_input
from .compiler import digest
from .dependency import failed_premise
from .engine import BridgeError, BridgeTimeout, run_bridge
from .model import ReplayProgram, ReplayResult


def replay(program: ReplayProgram, input_value, commands, *, timeout=10):
    if not isinstance(program, ReplayProgram):
        raise TypeError('replay requires a checked ReplayProgram')
    model = program.model
    if digest(model.source) != model.source_sha256 or digest(model.config) != model.config_sha256:
        return ReplayResult('execution_error', {}, 0, 'fixed source or Property.toml changed')
    try:
        input_value = decode_input(input_value, model.inputs)
    except CodecError as error:
        return ReplayResult('execution_error', {}, 0, str(error))
    request = {'input': [input_value[field['name']] for field in model.inputs],
               'pre': model.precondition, 'goal': model.goal,
               'external': list(model.external),
               'projection': program.projection}
    with AdapterSession(program, commands, timeout=timeout) as adapters:
        try:
            def callback(event):
                return adapters.call(event['relation'], event['input'], event['fresh_id'])
            trace = run_bridge('replay', model.source, request,
                               timeout=timeout, callback=callback)
            if trace.get('al_md5') != program.analysis['al_md5']:
                raise BridgeError('executed AL differs from compiled replay AL')
            status = trace.get('status')
            if status == 'precondition_failed':
                trace['failure'] = failed_premise(trace)
                status = ('implementation_bug' if trace['failure']['external_events']
                          else 'execution_error')
            elif status not in ('passed', 'failed'):
                status = 'execution_error'
            return ReplayResult(status, trace, adapters.call_count,
                                trace.get('failure', {}).get('reason', ''))
        except (AdapterTimeout, BridgeTimeout) as error:
            return ReplayResult('unknown', {}, adapters.call_count, str(error))
        except (AdapterProtocolError, BridgeError, OSError, ValueError) as error:
            return ReplayResult('execution_error', {}, adapters.call_count, str(error))
