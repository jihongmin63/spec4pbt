"""Command line for building, running, collecting and rechecking property clauses."""
import argparse
from dataclasses import asdict
import json
from pathlib import Path
import sys
import tomllib
from translator.toolchain import PROJECT
from pbt.property.clause import build_property,load_bundle,load_clause,strict_json
from pbt.property.plan import compile_clause,select_external
from pbt.property.runner import collect_case,recheck_trace,rerun_case,run_property


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    commands=parser.add_subparsers(dest='action',required=True)
    for action in ['inspect','plan','build']:
        p=commands.add_parser(action)
        p.add_argument('--spec',action='append',type=Path,required=True)
        p.add_argument('--property',type=Path,required=True)
        p.add_argument('--name',required=True)
        p.add_argument('--timeout',type=float,default=120)
        if action!='inspect':
            p.add_argument('--config',type=Path,required=True)
            p.add_argument('--external',type=Path,required=True)
        if action=='build':
            p.add_argument('--output',type=Path,required=True)
            p.add_argument('--transport-model',type=Path)
            p.add_argument('--proof-module',required=True)
            p.add_argument('--property-proof',required=True)
    for action in ['run','collect','recheck','rerun']:
        p=commands.add_parser(action)
        p.add_argument('--bundle',type=Path,required=True)
        p.add_argument('--timeout',type=float,default=120)
        if action in ['run','collect','rerun']:
            p.add_argument('--output',type=Path,required=True)
            p.add_argument('--implementation',type=Path,required=True)
            p.add_argument('--adapter-timeout',type=float,default=10)
        if action=='run':
            p.add_argument('--generator-module',required=True)
            p.add_argument('--generator',required=True)
            p.add_argument('--count',type=int,default=100)
            p.add_argument('--size',type=int,default=10)
            p.add_argument('--seed',type=int,default=0)
        if action=='collect':p.add_argument('--input',type=Path,required=True)
        if action=='recheck':p.add_argument('--trace',type=Path,required=True)
        if action=='rerun':p.add_argument('--case',type=Path,required=True)
    args=parser.parse_args()
    try:
        if args.action in ['inspect','plan']:
            clause=load_clause(args.spec,args.property,args.name,timeout_seconds=args.timeout)
            if args.action=='plan':
                with args.config.open('rb') as f:config=tomllib.load(f)
                with args.external.open('rb') as f:selection=tomllib.load(f)
                clause=compile_clause(clause,select_external(config,selection))
            print(json.dumps(clause,indent=2,ensure_ascii=False));return 0
        if args.action=='build':
            b=build_property(spec_paths=args.spec,property_path=args.property,config_path=args.config,
                             external_path=args.external,name=args.name,
                             output=args.output,timeout_seconds=args.timeout,transport_model=args.transport_model,
                             proof_module=args.proof_module,property_proof=args.property_proof)
            print(json.dumps({'bundle':str(b.directory),'namespace':b.namespace,'plan_id':b.plan['plan_id']}));return 0
        b=load_bundle(args.bundle,timeout_seconds=args.timeout)
        if args.action=='run':
            result=run_property(b,implementation=args.implementation,generator_module=args.generator_module,generator=args.generator,output=args.output,
                                count=args.count,size=args.size,seed=args.seed,timeout_seconds=args.timeout,adapter_timeout_seconds=args.adapter_timeout)
        elif args.action=='collect':result=collect_case(b,strict_json(args.input.read_text()),args.output,implementation=args.implementation,timeout_seconds=args.adapter_timeout)
        elif args.action=='recheck':result=recheck_trace(b,args.trace)
        else:result=rerun_case(b,args.case,args.output,implementation=args.implementation,timeout_seconds=args.adapter_timeout)
        print(json.dumps(asdict(result),default=str,ensure_ascii=False))
        status=getattr(result,'status',getattr(result,'verdict',None))
        return 0 if status in ['pass','passed'] else 3 if status=='error' else 2
    except (OSError,ValueError,ChildProcessError,TimeoutError) as e:
        print(str(e),file=sys.stderr);return 3


if __name__=='__main__':raise SystemExit(main())
