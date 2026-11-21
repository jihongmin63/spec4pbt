#!/usr/bin/env python3
"""Verify predicate equivalence, derive a generator, and run reproducible samples."""
import argparse
import json
from pathlib import Path
import re
import sys

from check import CheckError, Session, COQ_FLAGS, module, nonnegative, positive

PRELUDE = '''From QuickChick Require Import QuickChick.
From Coq Require Import List ZArith String.
Import ListNotations QcDefaultNotation.
Open Scope qc_scope.
'''


def derivation(candidate):
    target = module(candidate)
    return PRELUDE + f'''Require Sequence.
Import Property.Original.
Require Import {target}.
Derive ArbitrarySizedSuchThat for (fun x => predicate x).
Definition generator : G (option Property.Original.Input) :=
  @arbitraryST _ (fun x => {target}.predicate x) _.
'''


def extraction(samples, size):
    return PRELUDE + f'''Require Derived.
Fixpoint sample_seeds (n : nat) (seed : RandomSeed) : list RandomSeed :=
  match n with
  | O => nil
  | S m => let '(r1, r2) := randomSplit seed in r1 :: sample_seeds m r2
  end.
Definition rendered (seed : RandomSeed) : list (option string) :=
  List.map (fun r =>
    match run Derived.generator {size} r with
    | Some x => Some (show x)
    | None => None
    end) (sample_seeds {samples} seed).
Extraction "samples.ml" rendered.
'''


# Print Show representations as JSON strings; None remains JSON null.
DRIVER = r'''
let json_string chars =
  print_char '"';
  List.iter (fun c -> match c with
    | '"' -> print_string "\\\""
    | '\\' -> print_string "\\\\"
    | c when Char.code c < 32 || Char.code c > 126 ->
        Printf.printf "\\u%04x" (Char.code c)
    | c -> print_char c) chars;
  print_char '"'
let () =
  print_char '[';
  List.iteri (fun i item ->
    if i > 0 then print_char ',';
    match item with None -> print_string "null" | Some chars -> json_string chars
  ) (Samples.rendered (Random.State.make [| SAMPLER_SEED |]));
  print_endline "]"
'''


def normalize_extraction(directory):
    """Apply the pinned upstream integer-alias workaround to both extracted files."""
    changed = []
    for extension in ['ml', 'mli']:
        path = directory / f'samples.{extension}'
        original = path.read_text()
        normalized = re.sub(r'\btype int =\s*int\b',
                            'type qc_runtime_int = int\ntype int = qc_runtime_int', original)
        if normalized != original:
            (directory / f'samples.extracted.{extension}').write_text(original)
            path.write_text(normalized)
            changed.append(path.name)
    return changed


def execute(session, candidate, samples, size, seed, derive_only=False):
    session.report.update(candidate=candidate, samples=samples, size=size, seed=seed, derive_only=derive_only)
    session.check()
    (session.sources / 'Derived.v').write_text(derivation(candidate))
    session.compile('Derived.v', 'derivation')
    # The branch checks predicate equivalence, but does not certify generators.
    session.report['generator_proof'] = 'not_checked'
    session.command(['coqchk', '-silent', *COQ_FLAGS, 'Derived'], 'generator-kernel')
    session.fresh()
    if derive_only:
        return
    (session.sources / 'ExtractSamples.v').write_text(extraction(samples, size))
    session.compile('ExtractSamples.v', 'extraction')
    session.report['normalized_extraction_files'] = normalize_extraction(session.sources)
    # Unlike the upstream Sample command, compile the extracted interface as well.
    session.command(['ocamlfind', 'ocamlopt', '-package', 'zarith,unix', '-linkpkg', '-rectypes', '-w', '-a', '-c', 'samples.mli'], 'compile-interface')
    (session.sources / 'driver.ml').write_text(DRIVER.replace('SAMPLER_SEED', str(seed)))
    session.command(['ocamlfind', 'ocamlopt', '-package', 'zarith,unix', '-linkpkg', '-rectypes', '-w', '-a', 'samples.ml', 'driver.ml', '-o', 'sampler'], 'compile-executable')
    session.fresh()
    output = session.command([str(session.sources / 'sampler')], 'execution', coq=False)
    try:
        values = json.loads(output)
    except json.JSONDecodeError as error:
        raise CheckError(f'Invalid sampler output: {error}') from error
    if not isinstance(values, list) or len(values) != samples or any(x is not None and not isinstance(x, str) for x in values):
        raise CheckError('Sampler did not return the requested number of values')
    (session.directory / 'samples.json').write_text(json.dumps(values, indent=2) + '\n')
    session.report.update(generated=sum(x is not None for x in values), failed=sum(x is None for x in values))
    session.fresh()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('property', type=Path)
    parser.add_argument('--candidate', required=True, help='candidate directory, e.g. v002')
    parser.add_argument('--samples', type=positive, default=100)
    parser.add_argument('--size', type=nonnegative, default=30)
    parser.add_argument('--seed', type=nonnegative, default=0)
    parser.add_argument('--timeout', type=positive, default=120, help='seconds per subprocess')
    parser.add_argument('--derive-only', action='store_true', help='derive without sampling or generator proofs; no Show instance needed')
    args = parser.parse_args()
    session = None
    try:
        session = Session(args.property, selected=args.candidate, timeout=args.timeout)
        execute(session, args.candidate, args.samples, args.size, args.seed, args.derive_only)
        print(f'Equivalence checked; generator derived for {args.candidate}: {session.finish()}')
        return 0
    except (CheckError, OSError, UnicodeError) as error:
        if session:
            print(f'Report: {session.finish(error)}', file=sys.stderr)
        print(error, file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
