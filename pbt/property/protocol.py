"""Strict external-call protocol. This module does not evaluate properties."""
import subprocess
from pbt.lean_tools import require_timeout, timeout_output
from pbt.property.clause import strict_json

IDENTITIES=('plan_id','case_id','occurrence_id','relation_id')


def validate_response(response, request):
    """Apply the same wire contract to live and saved adapter responses."""
    if not isinstance(response,dict): raise ValueError('adapter response must be an object')
    for key in IDENTITIES:
        if response.get(key)!=request[key]: raise ValueError('adapter response identity mismatch: '+key)
    status=response.get('status')
    if status not in ('success','relation_failure'): raise ValueError('invalid adapter relation status')
    expected=set(IDENTITIES)|{'status'}|({'observation'} if status=='success' else set())
    if set(response)!=expected: raise ValueError('invalid adapter response fields')
    if status=='success' and (not isinstance(response['observation'],dict) or set(response['observation'])!=set(request['observe'])):
        raise ValueError('adapter observation selectors mismatch')
    return response


def execute(adapter, request, *, cwd, timeout_seconds):
    """Return a validated normal response, raw process evidence, and any I/O error."""
    process={'command':list(adapter),'cwd':str(cwd),'timeout_seconds':timeout_seconds}
    try:
        result=subprocess.run(adapter,cwd=cwd,text=True,capture_output=True,
                              input=__import__('json').dumps(request,allow_nan=False),
                              timeout=require_timeout(timeout_seconds),check=False)
        process.update(returncode=result.returncode,stdout=result.stdout,stderr=result.stderr)
        if result.returncode: raise ValueError(f'adapter exited with status {result.returncode}')
        response=strict_json(result.stdout)
        return validate_response(response,request),process,None
    except subprocess.TimeoutExpired as e:
        process.update(timeout=True,stdout=timeout_output(e.stdout),stderr=timeout_output(e.stderr))
        error=f'adapter timeout after {timeout_seconds}s'
    except (OSError,ValueError) as e:
        error=str(e)
    process['error']=error
    return None,process,error
