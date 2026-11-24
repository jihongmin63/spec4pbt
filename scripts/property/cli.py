"""Prepare, sample, replay, and debug an Input-only property workflow."""
import argparse
from pathlib import Path


def execute(args):
    if (getattr(args, 'spec', None) is not None or
            (args.property / '.runs/property-context.json').exists() or
            (args.property / '.runs/fixed-original-v2.json').exists() or
            not (args.property / 'Property.toml').exists()):
        from .commands import execute as run
    else:
        from .legacy import execute as run
    return run(args)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('property', type=Path)
    parser.add_argument('--spec', type=Path, help='shared Specification.toml (first prepare)')
    parser.add_argument('--implementation', type=Path, help='shared Adapter.toml for replay')
    sub = parser.add_subparsers(dest='action', required=True)
    prepare = sub.add_parser('prepare')
    prepare.add_argument('--target', choices=('spec', 'replay', 'debug'), default='spec')
    sample = sub.add_parser('sample')
    sample.add_argument('--candidate', required=True)
    sample.add_argument('--count', type=int, default=100)
    sample.add_argument('--size', type=int, default=30)
    sample.add_argument('--seed', type=int, default=0)
    for action in ('replay', 'debug'):
        command = sub.add_parser(action)
        command.add_argument('--samples-file', type=Path)
        command.add_argument('--input-json')
        command.add_argument('--timeout', type=float, default=10)
    for command in sub.choices.values():
        command.add_argument('--spec', type=Path, default=argparse.SUPPRESS)
        command.add_argument('--implementation', type=Path, default=argparse.SUPPRESS)
    args = parser.parse_args()
    path, ok = execute(args)
    print(path)
    return 0 if ok else 1


if __name__ == '__main__':
    raise SystemExit(main())
