"""Small external Copy adapter for the ordered property examples."""
import argparse
import json
from pathlib import Path
import subprocess
import sys


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--mode',choices=['correct','zero','reject'],default='correct')
    args=parser.parse_args()
    request=json.load(sys.stdin)
    response={key:request[key] for key in ('plan_id','case_id','occurrence_id','relation_id')}
    # The implementation accepts a native object; this adapter translates the
    # canonical relation input and extracts only the requested observation.
    target=Path(__file__).with_name('ordered_target.py')
    result=subprocess.run([sys.executable,str(target),'--mode',args.mode],
                          input=json.dumps({'number':request['input'][0]}),
                          capture_output=True,text=True,check=True)
    native=json.loads(result.stdout)
    if not native['ok']:
        response['status']='relation_failure'
    else:
        response['status']='success'
        response['observation']={selector:native['value'] for selector in request['observe']}
    print(json.dumps(response))


if __name__=='__main__':main()
