import Veir.PatternRewriter.Puddle.PrettyPrinter
import Veir.InstSimplify.IS0609
import Veir.InstSimplify.IS5150
import Veir.InstSimplify.IS3341

open Veir Veir.Puddle Veir.Data

namespace PuddlePrintingTest

-- Check important fragments without fixing Lean's incidental formatting of large predicates.
open Lean Elab Command Meta in
elab "#guard_puddle " rule:term " contains " expected:str : command => runTermElabM fun _ => do
  let type ← mkAppM ``Pattern #[mkConst ``OpCode]
  let rule ← Term.elabTermAndSynthesize rule (some type)
  let text := (← PrettyPrinter.format (← instantiateMVars rule)).pretty
  unless (text.splitOn expected.getString).length > 1 do
    throwError "missing fragment {expected.getString}\nin:\n{text}"

private def addZero : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let zero ← MatchProg.operation (.arith .constant) #[] #[ty]
      (fun p => p.value.value == 0)
    let _ ← MatchProg.root (.arith .addi) #[x, zero.res[0]!] #[ty]
    return x)
  pure (fun x => x)

/--
info: arith: (X + 0)  =>  X
where
  C0 = 0 : T0
  P0 = properties(C0)
  root = (X + C0) : T0
  P1 = properties(root)
  X : T0
  require P0.value.value == 0
  T0 : IntegerType
-/
#guard_msgs in
#print_puddle addZero

private def duplicate : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let inner ← MatchProg.operation (.llvm .add) #[x, y] #[ty]
    let _ ← MatchProg.root (.llvm .sub) #[inner.res[0]!, inner.res[0]!] #[ty]
    return (ty, x))
  (fun (ty, x) => do
    let p ← CreateProg.property (.llvm .sub) (default : NswNuwProperties)
    CreateProg.operation (.llvm .sub) #[x, x] #[ty] p)
  (fun op => op)

/--
info: llvm: (a0 - a0)  =>  (X - X)
where
  a0 = (X + Y) : T0
  P0 = properties(a0)
  root = (a0 - a0) : T0
  P1 = properties(root)
  new2 = (X - X) : T0 [created]
  P2 = properties(new2)
  X : T0
  Y : T0
  T0 : IntegerType
  P2 = { nsw := false, nuw := false }
-/
#guard_msgs in
#print_puddle duplicate

private def native : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 32)
    let x ← MatchProg.value ty
    let root ← MatchProg.root (.llvm .add) #[x, x] #[ty]
    MatchProg.matchNative (ty, root.properties) (fun (_, p) => !p.nsw)
    let extra ← MatchProg.inspectOperation (Outputs := Handle OpCode .type) root.op
      (fun _ _ => some (IntegerType.signless 64))
    return (ty, extra, x, root.properties))
  (fun (ty, extra, x, props) => do
    let (ty, props) ← CreateProg.applyNative (ty, props)
      (fun (t, p) => some (t, { p with nuw := false }))
    let _ ← CreateProg.type (IntegerType.signless 8)
    let _ ← CreateProg.operation (.llvm .add) #[x, x] #[extra] props
    CreateProg.operation (.llvm .add) #[x, x] #[ty] props)
  (fun op => op)

#guard_puddle native contains "require !P0.nsw"
#guard_puddle native contains "T1 ← inspect root using"
#guard_puddle native contains "(T2, P1) ← some (T0, { nsw := P0.nsw, nuw := false })"
-- Even an unused creation is part of the rewrite and must remain visible.
#guard_puddle native contains "new1 = (X + X) : T1 [created]"
#guard_puddle native contains "new2 = (X + X) : T2 [created]"
#guard_puddle native contains "T3 = TypeAttr.of IntegerType (IntegerType.signless 8)"

private def multiResult : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let _ ← MatchProg.root (.arith .addui_extended) #[x, y] #[ty, ty]
    return (x, y))
  pure (fun (x, y) => #[y, x])

#guard_puddle multiResult contains "addui_extended(X, Y)  =>  (Y, X)"
#guard_puddle multiResult contains "root = addui_extended(X, Y) : (T0, T0)"

private def erase : Pattern OpCode := Pattern.Builder
  (do
    let _ ← MatchProg.root (.test .test) #[] #[]
    return ())
  pure (fun _ => (#[] : Array (Handle OpCode .value)))

#guard_puddle erase contains "test: test()  =>  ()"
#guard_puddle Veir.InstSimplify.IS0609.pattern contains "llvm: (X + 0)  =>  X"
#guard_puddle Veir.InstSimplify.IS0609.pattern contains "require InstSimplify.bitConstantGuard T0 P0 0"
#guard_puddle Veir.InstSimplify.IS5150 contains "llvm: select(X, 1, 0)  =>  X"
#guard_puddle Veir.InstSimplify.IS5150 contains "t.bitwidth == 1"
#guard_puddle Veir.InstSimplify.IS3341_mulUdiv 2 8 contains "icmp(udiv((X * 2), 8), X)  =>  0"
#guard_puddle Veir.InstSimplify.IS3341_mulUdiv 2 8 contains "require P4.predicate == LLVM.IntPred.ugt"

-- Independent operations that happen to have the same expression stay distinct.
private def independent (swap : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let a ← MatchProg.operation (.llvm .add) #[x, y] #[ty] (fun p => p.nsw)
    let b ← MatchProg.operation (.llvm .add) #[x, y] #[ty] (fun p => p.nuw)
    let _ ← MatchProg.root (.llvm .sub)
      (if swap then #[b.res[0]!, a.res[0]!] else #[a.res[0]!, b.res[0]!]) #[ty]
    return x)
  pure (fun x => x)

#guard_puddle independent false contains "llvm: (a0 - a1)  =>  X"
#guard_puddle independent true contains "llvm: (a1 - a0)  =>  X"
#guard_puddle independent false contains "root = (a0 - a1) : T0"
#guard_puddle independent true contains "root = (a1 - a0) : T0"
#guard_puddle independent false contains "P0 = properties(a0)"
#guard_puddle independent false contains "P1 = properties(a1)"
#guard_puddle independent false contains "require P0.nsw"
#guard_puddle independent false contains "require P1.nuw"

-- Multiple results from a non-root operation retain their projection numbers.
private def projectResults : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let pair ← MatchProg.operation (.arith .addui_extended) #[x, x] #[ty, ty]
    let _ ← MatchProg.root (.arith .addi) #[pair.res[0]!, pair.res[1]!] #[ty]
    return pair.res[1]!)
  pure (fun x => x)

#guard_puddle projectResults contains "arith: (a0.0 + a0.1)  =>  a0.1"

private def lower : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let root ← MatchProg.root (.llvm .add) #[x, x] #[ty]
    return (ty, x, root.properties))
  (fun (ty, x, props) => do
    let props ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.gmir .g_add))) props
      (fun p => some p)
    CreateProg.operation (.gmir .g_add) #[x, x] #[ty] props)
  (fun op => op)

#guard_puddle lower contains "llvm.add(X, X)  =>  gmir.g_add(X, X)"
#guard_puddle lower contains "P1 ← some P0"

private def guardedConstant : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let c ← MatchProg.operation (.arith .constant) #[] #[ty]
      (fun p => p.value.value == 0 || p.value.value == 1)
    let _ ← MatchProg.root (.arith .addi) #[c.res[0]!, c.res[0]!] #[ty]
    return c.res[0]!)
  pure (fun x => x)

-- A predicate accepting several constants must not be guessed to mean one of them.
#guard_puddle guardedConstant contains "C0 = constant()"
#guard_puddle guardedConstant contains "require P0.value.value == 0 || P0.value.value == 1"

section
variable (n : Int)
-- Symbolic parameters in predicates survive, provided the graph itself is concrete.
#guard_puddle Veir.InstSimplify.IS3341_mulUdiv n 8 contains "(X * n)"
-- Compound symbolic constants keep their grouping when inlined into a summary.
#guard_puddle Veir.InstSimplify.IS3341_mulUdiv (n + 1) 8 contains "icmp(udiv((X * (n + 1)), 8), X)"
#guard_puddle Veir.InstSimplify.IS3341_mulUdiv (n + 1) 8 contains "C0 = (n + 1) : T0"
#guard_puddle Veir.InstSimplify.IS3341_mulUdiv (n + 1) 8 contains "a2 = (X * C0) : T0"
end

private def emptyMetadata : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let _ ← MatchProg.root (.llvm .add) #[x, x] #[ty]
    MatchProg.matchNative () (fun _ => true)
    return (ty, x))
  (fun (ty, x) => do
    let props ← CreateProg.applyNative () (fun _ => some (default : NswNuwProperties))
    CreateProg.operation (.llvm .add) #[x, x] #[ty] props)
  (fun op => op)

-- Empty native inputs reduce from Unit to PUnit during reflection.
#guard_puddle emptyMetadata contains "llvm: (X + X)  =>  new1"
#guard_puddle emptyMetadata contains "P1 ← some"

private def computed (n : Int) : Int := n + 1

private def computedConstant (n : Int) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let _ ← MatchProg.root (.arith .constant) #[] #[ty]
    return ty)
  (fun ty => do
    let props ← CreateProg.property (.arith .constant)
      (ArithConstantProperties.mk (.ofInt (computed n) (.signless 32)))
    CreateProg.operation (.arith .constant) #[] #[ty] props)
  (fun op => op)

section
variable (n : Int)
-- Keep the author's computation readable instead of unfolding integer arithmetic.
#guard_puddle computedConstant n contains "computed n"
end

private def createdCompound (n : Int) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let _ ← MatchProg.root (.arith .addi) #[x, x] #[ty]
    return (ty, x))
  (fun (ty, x) => do
    let props ← CreateProg.property (.arith .constant)
      (ArithConstantProperties.mk { value := n + 1, type := .signless 32 })
    let c ← CreateProg.operation (.arith .constant) #[] #[ty] props
    let props ← CreateProg.property (.arith .muli) default
    CreateProg.operation (.arith .muli) #[x, c.res[0]!] #[ty] props)
  (fun op => op)

section
variable (n : Int)
#guard_puddle createdCompound n contains "arith: (X + X)  =>  (X * (n + 1))"
#guard_puddle createdCompound n contains "new2 = (X * C1) : T0 [created]"
end

private def narrowConstant : Pattern OpCode := Pattern.Builder
  (do
    let narrow ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 8)
    let wide ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 32)
    let c ← MatchProg.operation (.llvm .mlir__constant) #[] #[wide]
    let _ ← MatchProg.root (.llvm .trunc) #[c.res[0]!] #[narrow]
    MatchProg.matchNative (narrow, c.properties)
      (fun (t, p) => InstSimplify.bitConstantGuard t p 0)
    return narrow)
  (fun narrow => do
    let props ← CreateProg.property (.llvm .mlir__constant)
      (LLVMConstantProperties.mk (.integer { value := 0, type := .signless 8 }))
    CreateProg.operation (.llvm .mlir__constant) #[] #[narrow] props)
  (fun op => op)

-- The guard accepts 256, so the i32 input cannot be printed as the literal zero.
#guard InstSimplify.bitConstantGuard (TypeAttr.of IntegerType (.signless 8))
  (LLVMConstantProperties.mk (.integer { value := 256, type := .signless 32 })) 0
#guard_puddle narrowConstant contains "llvm: trunc(C0)  =>  0"
#guard_puddle narrowConstant contains "C0 = mlir.constant() : T1"
#guard_puddle narrowConstant contains "require InstSimplify.bitConstantGuard T0 P0 0"

end PuddlePrintingTest
