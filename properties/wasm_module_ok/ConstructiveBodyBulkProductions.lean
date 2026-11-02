import properties.wasm_module_ok.ConstructiveBodyBulkCalls
import properties.wasm_module_ok.ConstructiveBodyIndexedTypes
import properties.wasm_module_ok.ConstructiveBodyIndexedProductions
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyBulkProductions
open SpecTec properties.wasm_module_ok ConstructiveBodyIndexedTypes ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveBodyIndexedProductions ConstructiveBodyBulkCalls

theorem copy_backed (c : context) (a b : addrtype) : ∀t∈copyInputs a b,CandidateValMatch.InTableVal c t :=
  cons_backed .NoEllipses (num_backed c _) (cons_backed .NoEllipses (num_backed c _)
    (cons_backed .NoEllipses (num_backed c _) (nil_backed c .NoEllipses)))
theorem init_backed (c : context) (a : addrtype) : ∀t∈initInputs a,CandidateValMatch.InTableVal c t :=
  cons_backed .NoEllipses (num_backed c _) (cons_backed .NoEllipses (num_backed c _)
    (cons_backed .NoEllipses (num_backed c _) (nil_backed c .NoEllipses)))

def tableCopy (c : context) (stack : inferresulttype) (env : Env c) (dest src : Table c)
    (hm : ConstructiveBodyReferenceMatcher.refMatch c src.rt dest.rt=true) : Production c stack :=
  fixed c stack env (.NoEllipses,copyInputs dest.addr src.addr) (.NoEllipses,[])
    (copy_backed c _ _) (nil_backed c .NoEllipses) (.«TABLE.COPY» dest.index src.index)
    (fun n => ConstructiveBodyBulkCalls.tableCopy c stack dest.index src.index dest.addr dest.lim dest.rt src.addr src.lim src.rt
      dest.lookup src.lookup (fun s => by
        rw [←hm]
        exact ConstructiveBodyReferenceMatcher.total c src.rt dest.rt s env.ready (src.backed env) (dest.backed env)) n)

def tableInit (c : context) (stack : inferresulttype) (env : Env c) (dest : Table c) (src : ConstructiveBodyLookup.Entry c.ELEMS)
    (hm : ConstructiveBodyReferenceMatcher.refMatch c src.value dest.rt=true) : Production c stack :=
  fixed c stack env (.NoEllipses,initInputs dest.addr) (.NoEllipses,[])
    (init_backed c _) (nil_backed c .NoEllipses) (.«TABLE.INIT» dest.index src.index)
    (fun n => ConstructiveBodyBulkCalls.tableInit c stack dest.index src.index dest.addr dest.lim dest.rt src.value
      dest.lookup src.lookup (fun s => by
        rw [←hm]
        exact ConstructiveBodyReferenceMatcher.total c src.value dest.rt s env.ready (env.elems src.value src.mem) (dest.backed env)) n)

def memoryCopy (c : context) (stack : inferresulttype) (env : Env c) (dest src : Memory c) : Production c stack :=
  fixed c stack env (.NoEllipses,copyInputs dest.addr src.addr) (.NoEllipses,[])
    (copy_backed c _ _) (nil_backed c .NoEllipses) (.«MEMORY.COPY» dest.index src.index)
    (ConstructiveBodyBulkCalls.memoryCopy c stack dest.index src.index dest.addr dest.lim src.addr src.lim dest.lookup src.lookup)

def memoryInit (c : context) (stack : inferresulttype) (env : Env c) (dest : Memory c) (src : Fin c.DATAS.length) : Production c stack :=
  fixed c stack env (.NoEllipses,initInputs dest.addr) (.NoEllipses,[])
    (init_backed c _) (nil_backed c .NoEllipses) (.«MEMORY.INIT» dest.index src.val)
    (ConstructiveBodyBulkCalls.memoryInit c stack dest.index src.val dest.addr dest.lim dest.lookup src.isLt)

-- Only existing type metadata is compared, before instruction construction.
def all (c : context) (stack : inferresulttype) (env : Env c) : List (Production c stack) :=
  ((ConstructiveBodyIndexedTypes.tables c).flatMap fun dest =>
    ((ConstructiveBodyIndexedTypes.tables c).flatMap fun src =>
      if hm : ConstructiveBodyReferenceMatcher.refMatch c src.rt dest.rt=true then [tableCopy c stack env dest src hm] else []) ++
    ((ConstructiveBodyLookup.entries c.ELEMS).flatMap fun src =>
      if hm : ConstructiveBodyReferenceMatcher.refMatch c src.value dest.rt=true then [tableInit c stack env dest src hm] else [])) ++
  ((ConstructiveBodyIndexedTypes.memories c).flatMap fun dest =>
    ((ConstructiveBodyIndexedTypes.memories c).map fun src => memoryCopy c stack env dest src) ++
    ((List.finRange c.DATAS.length).map fun src => memoryInit c stack env dest src))

#print axioms all
end properties.wasm_module_ok.ConstructiveBodyBulkProductions
