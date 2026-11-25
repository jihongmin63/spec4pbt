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
        return {'bindings': {}, 'control': set(), 'status': set(), 'returns': {}}

    def frame_sources(frame):
        marker, scope = frame['marker'], frame['scope']
        sources = set(scope['control'])
        sources.update(seq for seq in frame['external']
                       if external_relations[seq] == marker['kind'])
        if 'child_returns' in frame:
            # A completed helper can ignore an actual argument. Its status
            # summary, not the union of its arguments, explains negation.
            sources.update(frame.get('child_status', ()))
        else:
            for name in marker['inputs']:
                sources.update(scope['bindings'].get(name, ()))
        return sources

    def failed_sources(frames):
        sources = frame_sources(frames[-1]) if frames else set()
        # Negation succeeds only after all alternatives have failed. These
        # summaries are kept on the invocation, not in a fallback's scope.
        for frame in frames:
            if 'child_returns' not in frame:
                sources.update(frame.get('child_failures', ()))
        return sources

    def same_invocation(left, right):
        return left.get('invocation') == right.get('invocation')

    def current_scope(event):
        for frame in reversed(stack):
            if (frame['marker']['relation'] == event['relation'] and
                    same_invocation(frame['marker'], event) and
                    frame['marker']['kind'].startswith('path:')):
                return frame['scope']
        return root_scopes.setdefault(event['relation'], new_scope())

    for _, kind, event in timeline:
        if kind == 'external':
            fresh_sources.add(event['seq'])
            for frame in stack:
                if not frame['marker']['kind'].startswith('path:'):
                    frame['external'].add(event['seq'])
            continue
        key = (event['relation'], event['kind'], event['source'], event.get('invocation'))
        if event['phase'] == 'path_begin':
            prior = next((i for i in range(len(stack) - 1, -1, -1)
                          if stack[i]['marker']['relation'] == event['relation'] and
                          same_invocation(stack[i]['marker'], event) and
                          stack[i]['marker']['kind'].startswith('path:')), None)
            # Old evidence did not record native invocation IDs. Retain its
            # best-effort inference; new traces distinguish actual unwinding.
            recursive = 'invocation' not in event and prior is not None and any(
                frame['marker']['kind'] == event['relation']
                for frame in stack[prior + 1:])
            if prior is not None and not recursive:
                caller = next((frame for frame in reversed(stack[:prior])
                               if frame['marker']['kind'] == event['relation']), None)
                if caller is not None:
                    caller.setdefault('child_failures', set()).update(
                        failed_sources(stack[prior:]))
                del stack[prior:]
            scope = new_scope()
            caller = next((frame for frame in reversed(stack)
                           if frame['marker']['kind'] == event['relation'] and
                           not frame['marker']['kind'].startswith('path:')), None)
            if caller is not None:
                caller['child_started'] = True
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
                    caller['child_status'] = (completed['scope']['status'] |
                                              completed['scope']['control'])
                del stack[index:]
            continue
        if event['phase'] == 'return':
            scope = current_scope(event)
            sources = set(scope['control'])
            for name in event['inputs']:
                sources.update(scope['bindings'].get(name, ()))
            scope['returns'][int(event['kind'].split(':', 1)[1])] = sources
            continue
        if event['phase'] == 'before':
            stack.append({'key': key, 'marker': event, 'external': set(),
                          'scope': current_scope(event)})
            continue
        index = next((i for i in range(len(stack) - 1, -1, -1)
                      if stack[i]['key'] == key), None)
        if index is None:
            continue
        frame = stack[index]
        if event.get('negated'):
            # A successful negation has no path_end for the failing child.
            # Recover its failed premises before dropping their open frames.
            frame['child_status'] = (failed_sources(stack[index + 1:]) |
                                     frame.get('child_failures', set()))
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
        if 'child_returns' not in frame and not (event.get('negated') and frame.get('child_started')):
            for name in event['inputs']:
                sources.update(scope['bindings'].get(name, ()))
            if event['kind'].lower().startswith('fresh'):
                sources.update(fresh_sources)
        is_call = bool(direct_external) or 'child_returns' in frame or event.get('negated')
        status_sources = sources | frame.get('child_status', set())
        if is_call:
            scope['status'].update(status_sources)
        if event['kind'] == 'if' or (is_call and not event['outputs']):
            sources.update(status_sources)
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
    # Each entered helper receives its caller's control and per-argument data
    # dependencies. Classifying the actual failing premise avoids blaming an
    # unrelated argument that merely appears in an enclosing helper call.
    frame = stack[-1]
    failed = frame['marker']
    sources = frame_sources(frame)
    return {'relation': failed['relation'], 'premise': failed['kind'],
            'source': failed['source'], 'inputs': failed['inputs'],
            'external_events': sorted(sources), 'dependencies': edges,
            'reason': ('external_dependent_premise_failure' if sources
                       else 'unexpected_internal_premise_failure')}
