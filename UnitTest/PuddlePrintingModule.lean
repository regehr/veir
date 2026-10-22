module

import Veir.PatternRewriter.Puddle.PrettyPrinter

open Veir Veir.Puddle Veir.Data

namespace PuddlePrintingModuleTest

-- Ordinary module imports hide Array.range's implementation. Exercise the
-- printer without the catalog's preprocessing or an `import all` workaround.
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

private def createPair (ty : Handle OpCode .type) (x : Handle OpCode .value) :
    CreateProg.Builder CreatedOpHandle := do
  let props ← CreateProg.property (.arith .addui_extended) ()
  CreateProg.operation (.arith .addui_extended) #[x, x] #[ty, ty] props

private def swapResults : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let pair ← MatchProg.operation (.arith .addui_extended) #[x, x] #[ty, ty]
    let _ ← MatchProg.root (.arith .addui_extended) #[pair.res[1]!, pair.res[0]!] #[ty, ty]
    return (ty, x))
  (fun (ty, x) => createPair ty x)
  (fun pair => #[pair.res[1]!, pair.res[0]!])

/--
info: arith: addui_extended(a0.1, a0.0)  =>  (new2.1, new2.0)

where
  a0 = addui_extended(X, X) : (T0, T0)
  P0 = properties(a0)
  root = addui_extended(a0.1, a0.0) : (T0, T0)
  P1 = properties(root)
  new2 = addui_extended(X, X) : (T0, T0) [created]
  P2 = properties(new2)
  X : T0
  T0 : IntegerType
  P2 = PUnit.unit
-/
#guard_msgs in
#print_puddle swapResults

end PuddlePrintingModuleTest
