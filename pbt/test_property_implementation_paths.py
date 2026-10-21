"""Launcher and dependency paths must name exactly what executes."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from pbt.property_implementation import load_implementation

class ImplementationPathTests(unittest.TestCase):
    def setUp(self):
        self.temporary=tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root=Path(self.temporary.name)
        (self.root/'metadata-config.json').write_text(json.dumps({'schema_version':1,'observations':[{'id':'copy','relation':'Copy','observe':['%1']}]}))
        (self.root/'manifest.json').write_text(json.dumps({'relations':{'Copy':{}}}))
        self.bundle=SimpleNamespace(directory=self.root,plan={'calls':[{'relation':'Copy'}]})

    def manifest(self,command):
        path=self.root/'implementation.toml'
        path.write_text('schema_version=1\nid="A"\n[[executions]]\nrelation="Copy"\nadapter='+json.dumps(command)+'\n')
        return path

    def test_adapter_symlink_retarget_is_stale(self):
        (self.root/'one.py').write_text('print(1)\n')
        (self.root/'two.py').write_text('print(2)\n')
        script=self.root/'adapter.py'
        script.symlink_to('one.py')
        selected=load_implementation(self.manifest(['python3','adapter.py']),self.bundle)
        script.unlink()
        script.symlink_to('two.py')
        with self.assertRaisesRegex(ValueError,'stale'):
            selected.assert_fresh()

    def test_manifest_symlink_retarget_is_stale(self):
        (self.root/'adapter.py').write_text('print(1)\n')
        first=self.manifest(['python3','adapter.py'])
        second=self.root/'second.toml'
        second.write_text(first.read_text().replace('id="A"','id="B"'))
        selected_path=self.root/'selected.toml'
        selected_path.symlink_to(first.name)
        selected=load_implementation(selected_path,self.bundle)
        selected_path.unlink()
        selected_path.symlink_to(second.name)
        with self.assertRaisesRegex(ValueError,'stale'):
            selected.assert_fresh()

    def test_launcher_selected_at_preflight_is_executed_after_path_changes(self):
        first=self.root/'first';first.mkdir()
        second=self.root/'second';second.mkdir()
        for directory,number in [(first,1),(second,2)]:
            launcher=directory/'review-adapter'
            launcher.write_text('#!/bin/sh\nprintf "'+str(number)+'\\n"\n')
            launcher.chmod(0o755)
        manifest=self.manifest(['review-adapter'])
        original=os.environ.get('PATH','')
        with patch.dict(os.environ,{'PATH':str(first)+os.pathsep+original}):
            selected=load_implementation(manifest,self.bundle)
        with patch.dict(os.environ,{'PATH':str(second)+os.pathsep+original}):
            selected.assert_fresh()
            result=subprocess.run(selected.for_relation('Copy').adapter,cwd=selected.cwd,capture_output=True,text=True,check=True)
        self.assertEqual(result.stdout.strip(),'1')

    def test_relative_path_entries_resolve_in_implementation_cwd(self):
        launcher=self.root/'review-adapter'
        launcher.write_text('#!/bin/sh\nprintf "3\\n"\n')
        launcher.chmod(0o755)
        manifest=self.manifest(['review-adapter'])
        with patch.dict(os.environ,{'PATH':'.'}):
            try:
                selected=load_implementation(manifest,self.bundle)
            except ValueError as error:
                self.fail('valid implementation-cwd launcher was rejected: '+str(error))
            result=subprocess.run(selected.for_relation('Copy').adapter,cwd=selected.cwd,capture_output=True,text=True,check=True)
        self.assertEqual(result.stdout.strip(),'3')

if __name__=='__main__':unittest.main()
