"""Tiny Copy implementation with selectable behaviors for the example."""
import argparse
import json
import sys

parser=argparse.ArgumentParser()
parser.add_argument('--mode',choices=['correct','zero','reject'],required=True)
mode=parser.parse_args().mode
native=json.load(sys.stdin)
number=native['number']
print(json.dumps({'ok':mode!='reject','value':0 if mode=='zero' else number}))
