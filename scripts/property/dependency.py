"""Recover external data and control dependencies from native AL trace markers."""


def failed_premise(trace):
    markers = trace.get('markers', ())
    external = trace.get('external_calls', ())
    timeline = sorted([(item['seq'], 'marker', item) for item in markers] +
                      [(item['seq'], 'external', item) for item in external],
                      key=lambda event: event[0])
    stack = []
    root_scopes = {}
    edges = []
    fresh_sources = set()
    external_relations = {item['seq']: item['relation'] for item in external}
    def new_scope():
        return {'bindings': {}, 'control': set(), 'returns': {}}

    def current_scope(relation):
        for frame in reversed(stack):
            if (frame['marker']['relation'] == relation and
                    frame['marker']['kind'].startswith('path:')):
                return frame['scope']
        return root_scopes.setdefault(relation, new_scope())

    for _, kind, event in timeline:
        if kind == 'external':
            fresh_sources.add(event['seq'])
            for frame in stack:
                if not frame['marker']['kind'].startswith('path:'):
                    frame['external'].add(event['seq'])
            continue
        key = (event['relation'], event['kind'], event['source'])
        if event['phase'] == 'path_begin':
            prior = next((i for i in range(len(stack) - 1, -1, -1)
                          if stack[i]['marker']['relation'] == event['relation'] and
                          stack[i]['marker']['kind'].startswith('path:')), None)
            recursive = prior is not None and any(
                frame['marker']['kind'] == event['relation']
                for frame in stack[prior + 1:])
            if prior is not None and not recursive:
                del stack[prior:]
            scope = new_scope()
            caller = next((frame for frame in reversed(stack)
                           if frame['marker']['kind'] == event['relation'] and
                           not frame['marker']['kind'].startswith('path:')), None)
            if caller is not None:
                parent = caller['scope']
                scope['control'].update(parent['control'])
                actual_slots = caller['marker'].get('input_slots')
                formal_slots = event.get('input_slots')
                if actual_slots is None or formal_slots is None:
                    # Older evidence flattened argument boundaries. Its only
                    # available conservative mapping is the former union.
                    actual_slots = [caller['marker']['inputs']]
                    formal_slots = [event['inputs']]
                for actual, formal in zip(actual_slots, formal_slots):
                    inherited = set(parent['control'])
                    for name in actual:
                        inherited.update(parent['bindings'].get(name, ()))
                    for name in formal:
                        scope['bindings'][name] = set(inherited)
            stack.append({'key': key, 'marker': event, 'external': set(),
                          'scope': scope})
            continue
        if event['phase'] == 'path_end':
            index = next((i for i in range(len(stack) - 1, -1, -1)
                          if stack[i]['key'] == key), None)
            if index is not None:
                completed = stack[index]
                caller = next((frame for frame in reversed(stack[:index])
                               if frame['marker']['kind'] == event['relation'] and
                               not frame['marker']['kind'].startswith('path:')), None)
                if caller is not None:
                    caller['child_returns'] = completed['scope']['returns']
                    caller['child_control'] = set(completed['scope']['control'])
                del stack[index:]
            continue
        if event['phase'] == 'return':
            scope = current_scope(event['relation'])
            sources = set(scope['control'])
            for name in event['inputs']:
                sources.update(scope['bindings'].get(name, ()))
            scope['returns'][int(event['kind'].split(':', 1)[1])] = sources
            continue
        if event['phase'] == 'before':
            stack.append({'key': key, 'marker': event, 'external': set(),
                          'scope': current_scope(event['relation'])})
            continue
        index = next((i for i in range(len(stack) - 1, -1, -1)
                      if stack[i]['key'] == key), None)
        if index is None:
            continue
        frame = stack[index]
        del stack[index:]
        relation = event['relation']
        scope = frame['scope']
        # A successful helper's conditions select the continuation even when
        # the helper has no return slots. Failed alternatives never reach here.
        scope['control'].update(frame.get('child_control', ()))
        sources = set(scope['control'])
        direct_external = {seq for seq in frame['external']
                           if external_relations[seq] == event['kind']}
        sources.update(direct_external)
        if 'child_returns' not in frame:
            for name in event['inputs']:
                sources.update(scope['bindings'].get(name, ()))
            if event['kind'].lower().startswith('fresh'):
                sources.update(fresh_sources)
        if event['kind'] == 'if' and sources:
            scope['control'].update(sources)
        for slot, name in enumerate(event['outputs']):
            output_sources = set(sources)
            if 'child_returns' in frame:
                output_sources.update(frame['child_returns'].get(slot, ()))
            scope['bindings'][name] = output_sources
            if output_sources:
                edges.append({'binding': f'{relation}.{name}',
                              'external_events': sorted(output_sources),
                              'source': event['source']})
    if not stack:
        return {'reason': 'unexpected_internal_premise_failure',
                'external_events': [], 'dependencies': edges}
    sources = set()
    # Each entered helper receives its caller's control and per-argument data
    # dependencies. Classifying the actual failing premise avoids blaming an
    # unrelated argument that merely appears in an enclosing helper call.
    frame = stack[-1]
    failed = frame['marker']
    scope = frame['scope']
    sources.update(seq for seq in frame['external']
                   if external_relations[seq] == failed['kind'])
    sources.update(scope['control'])
    for name in failed['inputs']:
        sources.update(scope['bindings'].get(name, ()))
    return {'relation': failed['relation'], 'premise': failed['kind'],
            'source': failed['source'], 'inputs': failed['inputs'],
            'external_events': sorted(sources), 'dependencies': edges,
            'reason': ('external_dependent_premise_failure' if sources
                       else 'unexpected_internal_premise_failure')}
