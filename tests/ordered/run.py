"""Build and run certified ordered SpecTec property-clause examples."""
import argparse
import json
from pathlib import Path

from translator.toolchain import PROJECT
from tests import ORDERED
from pbt.property.clause import build_property
from pbt.property.runner import run_property

EXAMPLES={
    'positive':('copy_positive_proof.lean.in','copy_positive_generator.lean.in','ClauseCopy'),
    'chain':('copy_chain_proof.lean.in','copy_chain_generator.lean.in','ClauseChain'),
    'independent':('copy_chain_proof.lean.in','copy_chain_generator.lean.in','ClauseChain'),
    'internal_positive':('internal_positive_proof.lean.in','internal_positive_generator.lean.in','ClauseInternal'),
    'progress':('progress_proof.lean.in','progress_generator.lean.in','ClauseProgress'),
}


def build_example(name,output):
    if name not in EXAMPLES:raise ValueError('unknown ordered property example')
    output=Path(output).resolve()
    if not output.is_relative_to(PROJECT):raise ValueError('example output must be in the Lean project')
    output.parent.mkdir(parents=True,exist_ok=True)
    base='.'.join(output.relative_to(PROJECT).parts)
    root=ORDERED
    config=root/'observations.toml'
    proof_template,generator_template,proof_namespace=EXAMPLES[name]
    proof_module=base+'Proof'
    proof_path=output.parent/(output.name+'Proof.lean')
    if proof_path.exists():raise FileExistsError(proof_path)
    contract=base+'.Contract'
    proof=(root/'templates'/proof_template).read_text().replace('@CONTRACT@',contract)
    proof_path.write_text(proof)
    bundle=build_property(spec_paths=[root/'spec.watsup'],
        property_path=root/'properties.watsup',config_path=config,name=name,output=output,
        proof_module=proof_module,property_proof=proof_namespace+'.property_correct')
    generator=(root/'templates'/generator_template).read_text()
    generator=generator.replace('@CONTRACT@',contract).replace('@PROOF@',proof_module)
    (bundle.directory/'Generator.lean').write_text(generator)
    return bundle,base+'.Generator',proof_namespace+'Generator.generator'


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--property',choices=list(EXAMPLES),default='positive')
    parser.add_argument('--mode',choices=['correct','zero','reject'],default='correct')
    parser.add_argument('--bundle',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--count',type=int,default=4)
    parser.add_argument('--size',type=int,default=5)
    parser.add_argument('--seed',type=int,default=0)
    args=parser.parse_args()
    bundle,module,generator=build_example(args.property,args.bundle)
    result=run_property(bundle,generator_module=module,generator=generator,
        implementation=ORDERED/'implementations'/(args.mode+'.toml'),
        output=args.output,count=args.count,size=args.size,seed=args.seed)
    print(json.dumps({'status':result.status,'counts':result.counts,'output':str(result.output)}))
    return 0 if result.status=='passed' else 2


if __name__=='__main__':raise SystemExit(main())
