#!/usr/bin/env python3
"""Compile Wasm support and compare it with pinned, unchanged native arithmetic.
All donor extraction, OCaml objects, Coq objects, and evidence stay in ignored runs.
No external commands download or update sources; donor git object is read-only.
"""
from __future__ import annotations
import argparse, hashlib, json, random, re, shutil, subprocess, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parents[4]
TESTS = Path(__file__).resolve().parent
DONOR = '16142ff23b30611a3fba1bb0ceb0dd7928187d58'
MODULES = ['lib','utf8','pack','ixx','i8','i16','i32','i64','fxx','f32','f64','i32_convert','i64_convert','f32_convert','f64_convert','types','v128']

def execute(args, cwd, log, input=None):
    result = subprocess.run(list(map(str,args)), cwd=cwd, input=input, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log.write_text(result.stdout)
    if result.returncode:
        raise RuntimeError(f'{args}: exit {result.returncode}: {log}\n{result.stdout[-3500:]}')
    return result.stdout

def extract(run):
    native=run/'native';native.mkdir()
    files={}
    provenance=json.loads((TESTS/'PROVENANCE.json').read_text())
    for name,expected in provenance['donor_files'].items():
        data=subprocess.check_output(['git','show',DONOR+':'+name],cwd=ROOT)
        assert hashlib.sha256(data).hexdigest()==expected
        (run/Path(name).name).write_bytes(data)
        for chunk in data.decode().split('+++ b/')[1:]:
            head,*lines=chunk.splitlines();out=[]
            for line in lines:
                if line.startswith('diff ') or line.startswith('--- '):break
                if line.startswith('+') and not line.startswith('+++'):out.append(line[1:])
            files[Path(head).name]='\n'.join(out)+'\n'
    for name in MODULES:
        (native/(name+'.ml')).write_text(files[name+'.ml'])
    return native,files

def oracle_source(files):
    src='''let vec text = String.init 16 (fun i -> Char.chr (int_of_string ("0x" ^ String.sub text (2*(15-i)) 2)))
let output_vec v = for i=15 downto 0 do Printf.printf "%02x" (Char.code v.[i]) done; print_newline ()
let output32 n = Printf.printf "%lu\\n" n
let output64 n = Printf.printf "%Lu\\n" n
'''
    unary=['abs','neg','sqrt','ceil','floor','trunc','nearest']
    binary=['add','sub','mul','div','min','max','copysign']
    for w in [32,64]:
        for kind,ops in [('unary',unary),('binary',binary)]:
            src+=f'let f{w}_{kind} = function\n'
            for op in ops:src+=f' | "{op}" -> F{w}.{op}\n'
            src+=' | _ -> failwith "unknown float opcode"\n'
        src+=f'let f{w}_compare = function\n'
        for op in ['eq','ne','lt','le','gt','ge']:src+=f' | "{op}" -> F{w}.{op}\n'
        src+=' | _ -> failwith "unknown float comparison"\n'
    integer_binary={'Add':'add','Sub':'sub','Mul':'mul','DivS':'div_s','DivU':'div_u','RemS':'rem_s','RemU':'rem_u','And':'and_','Or':'or_','Xor':'xor','Shl':'shl','ShrS':'shr_s','ShrU':'shr_u','Rotl':'rotl','Rotr':'rotr'}
    integer_unary={'Clz':'clz','Ctz':'ctz','Popcnt':'popcnt','ExtendS8':'extend_s 8','ExtendS16':'extend_s 16','ExtendS32':'extend_s 32','ExtendS64':'extend_s 64'}
    integer_compare={'Eq':'eq','Ne':'ne','LtS':'lt_s','LtU':'lt_u','LeS':'le_s','LeU':'le_u','GtS':'gt_s','GtU':'gt_u','GeS':'ge_s','GeU':'ge_u'}
    for w in [32,64]:
        for kind,ops in [('binary',integer_binary),('unary',integer_unary),('compare',integer_compare)]:
            src+=f'let i{w}_{kind} = function\n'
            for name,fn in ops.items():src+=f' | "{name}" -> I{w}.{fn}\n'
            src+=' | _ -> failwith "unknown integer opcode"\n'
    families={}
    # Generate the test dispatcher only from native opcode branches. The numeric
    # functions invoked remain the unchanged donor implementations.
    text=files['eval_vec.ml']
    for family in ['testop','unop','binop','ternop','relop','cvtop','shiftop','bitmaskop']:
        section=text.split(f'  let {family} (op : {family})',1)[1].split('    in ',1)[0]
        branches=re.findall(r'\| (I8x16|I16x8|I32x4|I64x2|F32x4|F64x2) (\w+) -> (V128\.\w+\.\w+)\s*',section)
        assert branches,family
        families[family]=branches
        src+=f'let v_{family} shape op = match shape,op with\n'
        for shape,op,target in branches:src+=f' | "{shape}","{op}" -> {target}\n'
        src+=' | _ -> failwith "unknown vector opcode"\n'
    src+="let manual = function\n"
    shapes=['I8x16','I16x8','I32x4','I64x2','F32x4','F64x2']
    for shape in shapes:
        w=64 if shape in ['I64x2','F64x2'] else 32
        value=f'Int{w}.of_string x'
        if shape.startswith('F'):value=f'F{w}.of_bits ({value})'
        src+=f' | ["vsp";"{shape}";x] -> output_vec (V128.{shape}.splat ({value}))\n'
        src+=f' | ["vrp";"{shape}";a;i;x] -> output_vec (V128.{shape}.replace_lane (int_of_string i) (vec a) ({value}))\n'
        for sign in (['SX','ZX'] if shape in ['I8x16','I16x8'] else ['NONE']):
            fn='extract_lane' if shape.startswith('F') else ('extract_lane_s' if sign=='SX' else 'extract_lane_u')
            expr=f'V128.{shape}.{fn} (int_of_string i) (vec a)'
            if shape.startswith('F'):expr=f'F{w}.to_bits ({expr})'
            src+=f' | ["vex";"{shape}";"{sign}";a;i] -> output{w} ({expr})\n'
    src+=''' | ["vshuffle";a;b;idxs] -> output_vec (V128.V8x16.shuffle (vec a) (vec b) (List.map int_of_string (String.split_on_char ',' idxs)))
 | ["vv";"AnyTrue";a;_;_] -> print_endline (if V128.I8x16.any_true (vec a) then "1" else "0")
 | ["vv";"Not";a;_;_] -> output_vec (V128.V1x128.lognot (vec a))
 | ["vv";"And";a;b;_] -> output_vec (V128.V1x128.and_ (vec a) (vec b))
 | ["vv";"Or";a;b;_] -> output_vec (V128.V1x128.or_ (vec a) (vec b))
 | ["vv";"Xor";a;b;_] -> output_vec (V128.V1x128.xor (vec a) (vec b))
 | ["vv";"AndNot";a;b;_] -> output_vec (V128.V1x128.andnot (vec a) (vec b))
 | ["vv";"Bitselect";a;b;c] -> output_vec (V128.V1x128.bitselect (vec a) (vec b) (vec c))
 | _ -> failwith "invalid manual oracle request"
'''
    src+='''let run = function
 | ["ib";"32";op;a;b] -> output32 (i32_binary op (Int32.of_string a) (Int32.of_string b))
 | ["ib";"64";op;a;b] -> output64 (i64_binary op (Int64.of_string a) (Int64.of_string b))
 | ["iu";"32";op;a] -> output32 (i32_unary op (Int32.of_string a))
 | ["iu";"64";op;a] -> output64 (i64_unary op (Int64.of_string a))
 | ["ic";"32";op;a;b] -> print_endline (if i32_compare op (Int32.of_string a) (Int32.of_string b) then "1" else "0")
 | ["ic";"64";op;a;b] -> print_endline (if i64_compare op (Int64.of_string a) (Int64.of_string b) then "1" else "0")
 | ["fb";"32";op;a;b] -> output32 (F32.to_bits (f32_binary op (F32.of_bits (Int32.of_string a)) (F32.of_bits (Int32.of_string b))))
 | ["fb";"64";op;a;b] -> output64 (F64.to_bits (f64_binary op (F64.of_bits (Int64.of_string a)) (F64.of_bits (Int64.of_string b))))
 | ["fu";"32";op;a] -> output32 (F32.to_bits (f32_unary op (F32.of_bits (Int32.of_string a))))
 | ["fu";"64";op;a] -> output64 (F64.to_bits (f64_unary op (F64.of_bits (Int64.of_string a))))
 | ["fc";"32";op;a;b] -> print_endline (if f32_compare op (F32.of_bits (Int32.of_string a)) (F32.of_bits (Int32.of_string b)) then "1" else "0")
 | ["fc";"64";op;a;b] -> print_endline (if f64_compare op (F64.of_bits (Int64.of_string a)) (F64.of_bits (Int64.of_string b)) then "1" else "0")
 | ["fma";"32";a;b;c] -> output32 (F32.to_bits (F32.fma (F32.of_bits (Int32.of_string a)) (F32.of_bits (Int32.of_string b)) (F32.of_bits (Int32.of_string c))))
 | ["fma";"64";a;b;c] -> output64 (F64.to_bits (F64.fma (F64.of_bits (Int64.of_string a)) (F64.of_bits (Int64.of_string b)) (F64.of_bits (Int64.of_string c))))
 | ["convert";"32";a] -> output64 (F64.to_bits (F64_convert.promote_f32 (F32.of_bits (Int32.of_string a))))
 | ["convert";"64";a] -> output32 (F32.to_bits (F32_convert.demote_f64 (F64.of_bits (Int64.of_string a))))
 | ["vu";shape;op;a] -> output_vec (v_unop shape op (vec a))
 | ["vb";shape;op;a;b] -> output_vec (v_binop shape op (vec a) (vec b))
 | ["vr";shape;op;a;b] -> output_vec (v_relop shape op (vec a) (vec b))
 | ["vc";shape;op;a] -> output_vec (v_cvtop shape op (vec a))
 | ["vt";shape;op;a;b;c] -> output_vec (v_ternop shape op (vec a) (vec b) (vec c))
 | ["vs";shape;op;a;n] -> output_vec (v_shiftop shape op (vec a) (Int32.of_string n))
 | ["vtest";shape;op;a] -> print_endline (if v_testop shape op (vec a) then "1" else "0")
 | ["vmask";shape;op;a] -> output32 (v_bitmaskop shape op (vec a))
 | args -> manual args
let () = try while true do let line=read_line () in (try run (String.split_on_char ' ' line) with Ixx.Overflow | Ixx.DivideByZero | Ixx.InvalidConversion -> print_endline "TRAP" | exn -> Printf.printf "ERROR:%s\\n" (Printexc.to_string exn)) done with End_of_file -> ()
'''
    return src,families

def differential(run,native,files):
    src,families=oracle_source(files)
    (native/'oracle.ml').write_text(src)
    env=['bash',str(ROOT/'environment/env.sh'),'frontend']
    for name in MODULES:execute(env+['ocamlc','-w','-a','-c',name+'.ml'],native,native/(name+'.log'))
    execute(env+['ocamlc','-w','-a','-o','oracle']+[name+'.cmo' for name in MODULES]+['oracle.ml'],native,native/'oracle-build.log')
    requests=[];expressions=[];bases=[];case_records=[]
    def add(request,expression,base=10):
        requests.append(request);expressions.append(expression);bases.append(base)
    rng=random.Random(20261122)
    float_count=0
    for w in [32,64]:
        m=23 if w==32 else 52;e=8 if w==32 else 11
        inf=((1<<e)-1)<<m;sign=1<<(w-1);one=(127 if w==32 else 1023)<<m
        edge=[0,sign,1,sign+1,(1<<m)-1,1<<m,one,one+1,one+(1<<(m-1)),inf-1,inf,sign+inf,inf+1,sign+inf+1,inf+(1<<(m-1))]
        def bits(v):return hex(v)
        for op in ['add','sub','mul','div','min','max','copysign']:
            pairs=[(a,edge[(i*7+3)%len(edge)]) for i,a in enumerate(edge)]+[(rng.getrandbits(w),rng.getrandbits(w)) for _ in range(12)]
            for a,b in pairs:add(f'fb {w} {op} {bits(a)} {bits(b)}',f'WasmFloat.binary {w} "{op}" {a} {b}')
        for op in ['abs','neg','sqrt','ceil','floor','trunc','nearest']:
            for a in edge+[rng.getrandbits(w) for _ in range(12)]:add(f'fu {w} {op} {bits(a)}',f'WasmFloat.unary {w} "{op}" {a}')
        for op in ['eq','ne','lt','le','gt','ge']:
            for a in edge:
                b=rng.choice(edge);add(f'fc {w} {op} {bits(a)} {bits(b)}',f'(if WasmFloat.compare {w} "{op}" {a} {b} then 1 else 0)')
        for a in edge+[rng.getrandbits(w) for _ in range(12)]:
            b=rng.choice(edge);c=rng.choice(edge)
            add(f'fma {w} {bits(a)} {bits(b)} {bits(c)}',f'WasmFloat.fma {w} {a} {b} {c}')
            add(f'convert {w} {bits(a)}',f'WasmFloat.convert {w} {96-w} {a}')
    float_count=len(requests)
    integer_start=len(requests)
    for w in [32,64]:
        edge=[0,1,2,(1<<(w-1))-1,1<<(w-1),(1<<w)-2,(1<<w)-1]
        for op in ['Add','Sub','Mul','DivS','DivU','RemS','RemU','And','Or','Xor','Shl','ShrS','ShrU','Rotl','Rotr']:
            for a in edge:
                for b in [0,1,(1<<w)-1]:add(f'ib {w} {op} {hex(a)} {hex(b)}',f'integer_binary {w} "{op}" {a} {b}')
        for op in ['Clz','Ctz','Popcnt','ExtendS8','ExtendS16','ExtendS32','ExtendS64']:
            for a in edge:
                pack=int(op[7:]) if op.startswith('ExtendS') else 0
                normalized='ExtendS' if pack else op
                add(f'iu {w} {op} {hex(a)}',f'integer_unary {w} "{normalized}" {pack} {a}')
        for op in ['Eq','Ne','LtS','LtU','LeS','LeU','GtS','GtU','GeS','GeU']:
            for a in edge:
                b=rng.choice(edge);add(f'ic {w} {op} {hex(a)} {hex(b)}',f'map_outcome (fun (b : bool) => if b then 1 else 0) (integer_compare {w} "{op}" {a} {b})')
    integer_count=len(requests)-integer_start
    for family,branches in families.items():
        for shape,op,target in branches:
            w={'I8x16':8,'I16x8':16,'I32x4':32,'I64x2':64,'F32x4':32,'F64x2':64}[shape]
            floating=shape.startswith('F');fp='true' if floating else 'false'
            normalized=op.lower() if floating and family in ['unop','binop','relop'] else op
            for sample in range(3):
                a,b,c=[rng.getrandbits(128) for _ in range(3)]
                if sample==0:a,b,c=0,(1<<128)-1,int('80'*16,16)
                if sample==1:a,b,c=int('ff'*16,16),int('01'*16,16),0
                hx=lambda n:f'{n:032x}'
                if family=='testop':request=f'vtest {shape} {op} {hx(a)}';expr=f'WasmVector.eval_vtestop {w} {a}';base=10
                elif family=='bitmaskop':request=f'vmask {shape} {op} {hx(a)}';expr=f'WasmVector.eval_vbitmaskop {w} {a}';base=10
                elif family=='shiftop':
                    count=[0,257,4294967295][sample]
                    request=f'vs {shape} {op} {hx(a)} {hex(count)}';expr=f'WasmVector.eval_vshiftop {w} "{op}" {a} {count}';base=16
                else:
                    code={'unop':'vu','binop':'vb','relop':'vr','ternop':'vt','cvtop':'vc'}[family]
                    args=f'{hx(a)}';coqargs=f'{a}'
                    if family in ['binop','relop','ternop']:args+=f' {hx(b)}';coqargs+=f' {b}'
                    if family=='ternop':args+=f' {hx(c)}';coqargs+=f' {c}'
                    request=f'{code} {shape} {op} {args}'
                    expr=f'WasmVector.eval_v{family} {w} {fp} "{normalized}" '+('[] ' if family=='binop' else '')+coqargs
                    base=16
                # Results are naturally typed; project nat to Z only for testing.
                if family=='testop':expr=f'map_outcome Z.of_nat ({expr})'
                add(request,expr,base)
            case_records.append({'family':family,'shape':shape,'opcode':op,'native':target,'coq':'WasmVector.eval_v'+family,'samples':3})
    for shape in ['I8x16','I16x8','I32x4','I64x2','F32x4','F64x2']:
        w={'I8x16':8,'I16x8':16,'I32x4':32,'I64x2':64,'F32x4':32,'F64x2':64}[shape]
        sw=32 if w<64 else 64
        records=[('splat','NONE'),('replace','NONE')]+[('extract',s) for s in (['SX','ZX'] if w<32 else ['NONE'])]
        for family,sign in records:
            for sample in range(3):
                a=rng.getrandbits(128);x=rng.getrandbits(sw);i=[0,128//w-1,0][sample];hx=lambda n:f'{n:032x}'
                if family=='splat':request=f'vsp {shape} {hex(x)}';expr=f'WasmVector.eval_vsplatop {w} {sw} {x}';base=16
                elif family=='replace':request=f'vrp {shape} {hx(a)} {i} {hex(x)}';expr=f'WasmVector.eval_vreplaceop {w} {sw} {a} {i} {x}';base=16
                else:request=f'vex {shape} {sign} {hx(a)} {i}';expr=f'WasmVector.eval_vextractop {w} {str(sign=="SX").lower()} {a} {i}';base=10
                add(request,expr,base)
            case_records.append({'family':family,'shape':shape,'opcode':sign,'native':'V128.'+shape,'coq':'WasmVector.eval_v'+family+'op','samples':3})
    for sample in range(3):
        a,b=rng.getrandbits(128),rng.getrandbits(128);shuffle=[rng.randrange(32) for _ in range(16)]
        add(f'vshuffle {a:032x} {b:032x} '+','.join(map(str,shuffle)),f'WasmVector.eval_vbinop 8 false "Shuffle" ['+';'.join(str(i)+'%nat' for i in shuffle)+f'] {a} {b}',16)
    case_records.append({'family':'binop','shape':'I8x16','opcode':'Shuffle','native':'V128.V8x16.shuffle','coq':'WasmVector.eval_vbinop','samples':3})
    for op in ['AnyTrue','Not','And','Or','Xor','AndNot','Bitselect']:
        for sample in range(3):
            a,b,c=[rng.getrandbits(128) for _ in range(3)]
            if sample==0:a,b,c=0,0,0
            if op=='AnyTrue':expr=f'map_outcome Z.of_nat (WasmVector.eval_vvtestop {a})';base=10
            elif op=='Not':expr=f'WasmVector.eval_vvunop {a}';base=16
            elif op=='Bitselect':expr=f'WasmVector.eval_vvternop {a} {b} {c}';base=16
            else:expr=f'WasmVector.eval_vvbinop "{op}" {a} {b}';base=16
            add(f'vv {op} {a:032x} {b:032x} {c:032x}',expr,base)
        case_records.append({'family':'whole-vector','shape':'V128','opcode':op,'native':'V128.V1x128','coq':'WasmVector.eval_vv*','samples':3})
    output=execute([native/'oracle'],native,native/'oracle-results.txt',input='\n'.join(requests)+'\n').splitlines()
    assert len(output)==len(requests),(len(output),len(requests))
    proofs=['From Coq Require Import ZArith List String.','From ALCoq Require Import Execution.','From ALCoq.Builtins Require Import WasmScalar WasmFloat WasmVector.','Import ListNotations WasmScalar.','Open Scope string_scope.','Open Scope Z_scope.']
    for i,(expr,result,base) in enumerate(zip(expressions,output,bases)):
        assert not result.startswith('ERROR'),(requests[i],result)
        if result=='TRAP':
            proofs.append(f'Example native_{i:04} : (match {expr} with Error e => Some (error_kind e) | _ => None end) = Some NumericTrap. Proof. vm_compute. reflexivity. Qed.')
            continue
        expected=int(result,base)
        if i>=float_count:rhs=f'Success {expected}'
        else:rhs=str(expected)
        proofs.append(f'Example native_{i:04} : ({expr}) = {rhs}. Proof. vm_compute. reflexivity. Qed.')
    proofs.append('Print Assumptions native_0000.')
    (run/'NativeComparison.v').write_text('\n'.join(proofs)+'\n')
    (run/'native-cases.json').write_text(json.dumps([{'request':r,'coq':e,'expected':s,'base':b} for r,e,s,b in zip(requests,expressions,output,bases)],indent=2)+'\n')
    inventory={'native_revision':DONOR,'simd_opcode_branches':case_records,'simd_branch_count':len(case_records),'native_samples':len(requests),'float_samples':float_count,'integer_samples':integer_count,'simd_samples':len(requests)-float_count-integer_count}
    (run/'opcode-inventory.json').write_text(json.dumps(inventory,indent=2)+'\n')
    return inventory

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--run-dir',type=Path);args=parser.parse_args()
    base=ROOT/'_opam-testing-theorems/checks';base.mkdir(parents=True,exist_ok=True)
    run=args.run_dir.resolve() if args.run_dir else Path(tempfile.mkdtemp(prefix='wasm-builtins.',dir=base))
    if not run.is_relative_to(ROOT/'_opam-testing-theorems'):raise ValueError('evidence must be under target _opam-testing-theorems')
    run.mkdir(parents=True,exist_ok=True)
    report={'suite':'builtin-wasm','run':str(run),'status':'failed','sources':{}}
    print(f'Wasm builtin evidence: {run}',flush=True)
    try:
        native,files=extract(run)
        inventory=differential(run,native,files);report.update(inventory)
        print(f'Native samples: {inventory["native_samples"]}; SIMD opcode branches: {inventory["simd_branch_count"]}',flush=True)
        sources=['Execution.v','Values.v','Builtins/WasmScalar.v','Builtins/WasmFloat.v','Builtins/WasmVector.v','Builtins/WasmExecution.v']
        for name in sources:
            source=ROOT/'translator/coq'/name;target=run/name;target.parent.mkdir(exist_ok=True);shutil.copy2(source,target)
            report['sources'][name]=hashlib.sha256(source.read_bytes()).hexdigest()
        shutil.copy2(TESTS/'WasmBuiltins.v',run/'WasmBuiltins.v')
        for name in sources+['WasmBuiltins.v','NativeComparison.v']:
            print(f'Compiling {name}',flush=True)
            execute(['bash',ROOT/'environment/env.sh','coqc','-q','-Q',run,'ALCoq',name],run,run/(Path(name).stem+'.log'))
        report['status']='passed'
    finally:
        (run/'report.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
