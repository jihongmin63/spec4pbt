"""Prepare a property declaration and its fixed Coq input predicate."""
from dataclasses import dataclass, replace
from pathlib import Path
import re
import tempfile

from .bridge import ROOT
from .compiler import compile_spec
from .context import establish_context, file_hash, load_context, publication_hashes, validate_hashes
from .model import CompileError
from .setup import load_specification


@dataclass(frozen=True)
class PreparedProperty:
    model: object
    publication: Path
    specification: object
    context: dict


def write_source_once(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    try:
        with path.open('x') as stream:
            stream.write(text)
    except FileExistsError:
        if path.read_text() != text:
            raise ValueError(f'fixed source differs: {path}')


def initial_candidate(prop, original, namespace):
    candidate = prop / 'candidates/v001'
    if candidate.exists():
        return
    start = original.index('Inductive predicate')
    end = original.index('\n\n', start)
    header = ('Require Import Property.Original.\n'
              'From Coq Require Import String Ascii ZArith.\n'
              'From ALCoq Require Import Execution.\n'
              f'From {namespace}.Generated Require Import Types_0000 InductiveRelations.\n')
    write_source_once(candidate / 'Candidate.v', header + original[start:end] + '\n')
    write_source_once(candidate / 'Equivalence.v', '''Require Import Property.Original Property.candidates.v001.Candidate.
Theorem equivalent : forall x : Original.Input,
  Original.predicate x <-> Candidate.predicate x.
Proof.
  intro x; split; intro H; destruct H; econstructor; eassumption.
Qed.
''')


def prepare_property(property_dir, specification_manifest=None):
    """Create checked fixed artifacts once; subsequent calls validate their identity."""
    from .declaration import lower_property
    from .rocq import render_original, translate_property
    prop = Path(property_dir).resolve()
    if not prop.is_relative_to(ROOT) or not re.fullmatch(r'[A-Za-z0-9_][A-Za-z0-9_-]*', prop.name):
        raise ValueError('property directory must have a simple name inside this worktree')
    context = load_context(prop)
    if context is None:
        if specification_manifest is None:
            raise CompileError('first prepare requires --spec Specification.toml')
        if (prop / 'Property.toml').exists():
            raise CompileError('prepare the unified declaration in a new property directory')
        specification = load_specification(specification_manifest)
        runs = prop / '.runs'
        runs.mkdir(exist_ok=True)
        staging = Path(tempfile.mkdtemp(prefix='declaration-', dir=runs))
        property_source = prop / 'Property.spectec'
        authored_hashes = {**specification.hashes, str(property_source): file_hash(property_source)}
        lowered = lower_property(property_source, list(specification.sources), staging)
        validate_hashes(authored_hashes)
        publication = runs / 'publication'
        try:
            # Diagnose unsupported property forms before the translator snapshots
            # the input, so these errors retain the authored source mapping.
            compile_spec(lowered.source, lowered.config)
            translate_property(lowered.source, lowered.config, publication,
                               profile=specification.profile)
            original = render_original(lowered.source, lowered.config, publication=publication,
                                       public_input_names=lowered.source_map.get('variables', {}))
        except (CompileError, RuntimeError, ValueError) as error:
            from .declaration import remap_locations
            mapping = dict(lowered.source_map)
            rows = list(mapping['lines'])
            # Both existing translation passes use a private copy of the same
            # bytes. Alias diagnostic locations in that copy to the source map.
            for path in set(re.findall(r'(/[^\s:]+/' + re.escape(lowered.source.name) +
                                       r')(?=:\d)', str(error))):
                rows.extend({**row, 'generated_file': path} for row in mapping['lines']
                            if row['generated_file'] == str(lowered.source))
            mapping['lines'] = rows
            raise CompileError(remap_locations(str(error), mapping),
                               code=getattr(error, 'code', 'property_translation_error'),
                               details=remap_locations(getattr(error, 'details', None), mapping)) from error
        validate_hashes(authored_hashes)
        write_source_once(prop / 'Original.v', original)
        initial_candidate(prop, original, specification.namespace)
        hashes = {**authored_hashes, **publication_hashes(publication),
                  str(prop / 'Original.v'): file_hash(prop / 'Original.v'),
                  str(lowered.source.resolve()): file_hash(lowered.source),
                  str(lowered.config.resolve()): file_hash(lowered.config)}
        context = establish_context(prop, {
            'version': 2, 'property': str(prop), 'name': lowered.name,
            'specification': str(specification.manifest),
            'publication': str(publication.resolve()),
            'source': str(lowered.source.resolve()), 'config': str(lowered.config.resolve()),
            'source_map': lowered.source_map, 'semantic_hashes': hashes})
    specification = load_specification(context['specification'])
    if specification_manifest is not None:
        selected = load_specification(specification_manifest)
        if selected.manifest != specification.manifest:
            raise CompileError('selected specification differs from fixed property context')
    model = compile_spec(context['source'], context['config'])
    names = context['source_map'].get('variables', {})
    model = replace(model, inputs=tuple({**item, 'name': names.get(item['name'], item['name'])}
                                        for item in model.inputs),
                    source_map=context['source_map'], semantic_hashes=context['semantic_hashes'])
    return PreparedProperty(model, Path(context['publication']), specification, context)
