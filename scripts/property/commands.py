"""Coordinate prepare, sample, replay, and debug for shared property declarations."""
from collections import Counter
from dataclasses import asdict
import json
from pathlib import Path
import subprocess
import tempfile

from .bridge import ROOT
from .compiler import attach_implementation, compile_debug, compile_replay
from .context import load_context, load_inputs, tool_hashes, validate_hashes
from .debug import debug
from .generation import GenerationError, sample
from .model import CompileError
from .prepare import prepare_property
from .replay import replay
from .setup import load_implementation


def execute(args):
    """CLI entry point for declarations; legacy evidence uses the legacy path."""
    prop = Path(args.property).resolve()
    if not prop.is_relative_to(ROOT):
        raise ValueError('property must be inside this worktree')
    runs = prop / '.runs'
    runs.mkdir(parents=True, exist_ok=True)
    evidence = Path(tempfile.mkdtemp(prefix=args.action + '-', dir=runs))
    report = {'version': 2, 'action': args.action, 'property': str(prop),
              'status': 'running', 'generator_proof': 'not_checked'}
    model = None
    try:
        prepared = prepare_property(prop, getattr(args, 'spec', None))
        model = prepared.model
        tools = tool_hashes()
        report.update(input_fields=list(model.inputs),
                      semantic_hashes=prepared.context['semantic_hashes'],
                      tool_hashes=tools, publication=str(prepared.publication),
                      property_name=prepared.context['name'],
                      fixed_original=str(runs / 'fixed-original-v2.json'))
        is_replay = args.action == 'replay' or (
            args.action == 'prepare' and args.target == 'replay')
        implementation = None
        if is_replay:
            if getattr(args, 'implementation', None) is None:
                raise CompileError('replay requires --implementation Adapter.toml')
            implementation = load_implementation(args.implementation, prepared.specification)
            model = attach_implementation(model, implementation)
            report['implementation_hashes'] = dict(implementation.hashes)
        if args.action == 'prepare':
            report['target'] = args.target
            if args.target == 'replay':
                program = compile_replay(model)
                report['analysis'] = program.analysis
            elif args.target == 'debug':
                program = compile_debug(model)
                report.update(debug_available=program.available,
                              missing_definitions=list(program.missing), al_md5=program.al_md5)
        elif args.action == 'sample':
            report.update(sample(args, prepared, evidence, tools))
        else:
            values, batch_path = load_inputs(args, prop, prepared, tools)
            report.update(batch_evidence=batch_path, attempts=len(values))
            if is_replay:
                program = compile_replay(model)
                report['analysis'] = program.analysis
                run_one = lambda value: replay(program, value, implementation.commands,
                                                timeout=args.timeout)
            else:
                program = compile_debug(model)
                report.update(debug_available=program.available, al_md5=program.al_md5)
                run_one = lambda value: debug(program, value, timeout=args.timeout)
            results = []
            for index, value in enumerate(values):
                if value is None:
                    results.append({'attempt': index, 'status': 'no_generation'})
                else:
                    results.append({'attempt': index, 'input': value, **asdict(run_one(value))})
            path = evidence / 'results.json'
            path.write_text(json.dumps(results, indent=2) + '\n')
            report.update(results_file=str(path),
                          status_counts=dict(Counter(item['status'] for item in results)),
                          external_calls=sum(item.get('external_call_count', 0) for item in results))
            if batch_path is not None:
                load_inputs(args, prop, prepared, tools)
        load_context(prop)
        if tools != tool_hashes():
            raise ValueError('tools changed during command')
        if implementation is not None:
            validate_hashes(implementation.hashes)
        report['status'] = 'passed'
    except (CompileError, GenerationError, OSError, ValueError, RuntimeError,
            KeyError, subprocess.TimeoutExpired) as error:
        report.update(status='failed', error=str(error))
        if isinstance(error, CompileError):
            report['compile_error_code'] = error.code
            if error.details is not None:
                report['analysis_failure'] = error.details
    if model is not None and model.source_map:
        from .declaration import remap_locations
        for key in ('analysis', 'analysis_failure', 'error'):
            if key in report:
                report[key] = remap_locations(report[key], model.source_map)
    path = evidence / 'result.json'
    path.write_text(json.dumps(report, indent=2) + '\n')
    return path, report['status'] == 'passed'
