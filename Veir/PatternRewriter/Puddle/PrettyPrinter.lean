module

public import Veir.PatternRewriter.Puddle.Builders
public meta import Lean

/-!
# Reading Puddle rewrites

`#print_puddle rule` displays an existing `Pattern OpCode` as a rewrite, followed by
its types, property constraints, and native metadata computations. It reduces the
Puddle builders, not the source syntax: helper functions and instantiated pattern
families work too. Native functions are printed as Lean expressions, never sampled
or executed to guess their meaning.

The output is for people, not a serialization format. Shared operations have names
so that two uses of one matched operation cannot be confused with two independently
matched operations. Operation names retain their dialect, and result order matters.
-/

namespace Veir.Puddle
open Lean Meta Elab Command

-- Recognition templates, checked by definitional equality rather than by trying
-- a predicate on sample values. Unrecognized predicates remain explicit.
-- Their bodies must be exposed for reflection from clients using ordinary
-- module imports: the formatter refers to these declarations by name.
@[expose] public def PrettyPrinter.Templates.arithConstant (n : Int) (p : ArithConstantProperties) : Bool :=
  p.value.value == n

@[expose] public def PrettyPrinter.Templates.integerConstant (n : Int) (p : LLVMConstantProperties) : Bool :=
  match p.value with
  | .integer a => a.value == n
  | _ => false

@[expose] public def PrettyPrinter.Templates.bitConstant (n : Int) (input : TypeAttr × LLVMConstantProperties) : Bool :=
  match input.1.val, input.2.value with
  | .integerType t, .integer a =>
    BitVec.ofInt t.bitwidth a.value == BitVec.ofInt t.bitwidth n
  | _, _ => false

public meta section

namespace PrettyPrinter

private structure Operation where
  id : Nat
  opcode : String
  operands : Array Nat
  types : Array Nat
  results : Array Nat
  property : Nat
  created : Bool
  literal : Option String := none
  deriving Inhabited

private structure Metadata where
  id : Nat
  type : Expr
  name : String

private structure Description where
  root : Nat := 0
  operations : Array Operation := #[]
  leaves : Array (Nat × Nat) := #[]
  metadata : Array Metadata := #[]
  matchDecls : Array Expr := #[]
  createDecls : Array Expr := #[]
  replacements : Array Nat := #[]
  names : Std.HashMap Nat String := {}

private def constructor (e : Expr) (name : Name) : MetaM (Array Expr) := do
  let e ← whnf e
  unless e.isAppOf name do
    throwError "Puddle printer: expected {name}, got{indentExpr e}"
  return e.getAppArgs

private def nat (e : Expr) : MetaM Nat := do
  let reduced ← whnf e
  if let some n ← getNatValue? reduced then return n
  let reduced ← reduce ((← dsimp reduced (← Simp.mkContext {})).1)
  let some n ← getNatValue? (← whnf reduced)
    | throwError "Puddle printer needs concrete handle indices; instantiate parameters that determine the graph"
  return n

private def handle (e : Expr) : MetaM Nat := do
  nat (← constructor e ``Handle.mk).back!

private partial def list (e : Expr) : MetaM (Array Expr) := do
  let e ← whnf e
  if e.isAppOf ``List.nil then return #[]
  unless e.isAppOf ``List.cons do
    throwError "Puddle printer needs a concrete declaration list, got{indentExpr e}"
  let args := e.getAppArgs
  return #[args[1]!] ++ (← list args[2]!)

private def array (e : Expr) : MetaM (Array Expr) := do
  let args ← constructor e ``Array.mk
  list args.back!

private def handles (e : Expr) : MetaM (Array Nat) := do
  (← array e).mapM handle

private def opcodeName (e : Expr) : MetaM String := do
  -- These are the same dialect and mnemonic constructors used by OpCode.name.
  let e ← whnf e
  let some (.str ``OpCode dialect) := e.getAppFn.constName?
    | throwError "Puddle printer needs a concrete opcode, got{indentExpr e}"
  let op ← whnf e.getAppArgs.back!
  let some name := op.getAppFn.constName?
    | throwError "Puddle printer needs a concrete opcode, got{indentExpr op}"
  return dialect ++ "." ++ name.getString!.replace "__" "."

private def addMetadata (d : Description) (id : Nat) (type : Expr)
    (isType : Bool) : Description := Id.run do
  if d.metadata.any (·.id == id) then return d
  let stem := if isType then "T" else "P"
  let index := d.metadata.countP (·.name.startsWith stem)
  return { d with metadata := d.metadata.push ⟨id, type, stem ++ toString index⟩ }

/-- Traverse the same unit/atom/product metadata tuples accepted by Puddle. -/
private partial def metadataHandles (e : Expr) : MetaM (Array (Nat × Expr × Bool)) := do
  let type ← whnf (← inferType e)
  if type.isConstOf ``Unit || type.isConstOf ``PUnit then return #[]
  if type.isAppOf ``Prod then
    return (← metadataHandles (.proj ``Prod 0 e)) ++
      (← metadataHandles (.proj ``Prod 1 e))
  unless type.isAppOf ``Handle do
    throwError "Puddle printer: unsupported metadata tuple{indentExpr type}"
  let kind ← whnf type.getAppArgs.back!
  let id ← handle e
  if kind.isAppOf ``HandleType.type then
    return #[(id, mkConst ``TypeAttr, true)]
  unless kind.isAppOf ``HandleType.prop do
    throwError "Puddle printer: expected a metadata handle{indentExpr e}"
  return #[(id, ← mkAppM ``propertiesOf #[kind.getAppArgs.back!], false)]

private def addHandles (d : Description) (e : Expr) : MetaM Description := do
  let mut d := d
  for (id, type, isType) in ← metadataHandles e do
    d := addMetadata d id type isType
  return d

private def describe (rule : Expr) : MetaM Description := do
  let rule ← whnf rule
  let matcher := Expr.proj ``Pattern 1 rule
  let creation := Expr.proj ``Pattern 3 rule
  let mut d : Description := {
    root := ← handle (.proj ``MatchProg 0 matcher)
    matchDecls := ← list (.proj ``MatchProg 1 matcher)
    createDecls := ← list (.proj ``CreateProg 0 creation)
    replacements := ← handles (.proj ``Replacement 0 (.proj ``Pattern 4 rule))
  }
  -- Builder order gives stable, small names to leaves and metadata.
  for decl in d.matchDecls.reverse do
    let decl ← whnf decl
    let args := decl.getAppArgs
    match decl.getAppFn.constName? with
    | some ``MatchDecl.type =>
      d := ← addHandles d args.back!
    | some ``MatchDecl.value =>
      d := { d with leaves := d.leaves.push (← handle args.back!, ← handle args[args.size - 2]!) }
    | some ``MatchDecl.operation =>
      let a := args.extract (args.size - 8) args.size
      d := ← addHandles d a[4]!
      d := { d with operations := d.operations.push {
        id := ← handle a[5]!, opcode := ← opcodeName a[0]!, operands := ← handles a[1]!
        types := ← handles a[2]!, results := ← handles a[6]!, property := ← handle a[4]!
        created := false } }
    | some ``MatchDecl.applyNative => pure ()
    | some ``MatchDecl.inspectOperation => d := ← addHandles d args.back!
    | _ => throwError "Puddle printer: unsupported match declaration{indentExpr decl}"
  for decl in d.createDecls do
    let decl ← whnf decl
    let args := decl.getAppArgs
    match decl.getAppFn.constName? with
    | some ``CreateDecl.type | some ``CreateDecl.property => d := ← addHandles d args.back!
    | some ``CreateDecl.applyNative => d := ← addHandles d args.back!
    | some ``CreateDecl.operation =>
      let a := args.extract (args.size - 6) args.size
      d := { d with operations := d.operations.push {
        id := ← handle a[4]!, opcode := ← opcodeName a[0]!, operands := ← handles a[1]!
        types := ← handles a[2]!, results := ← handles a[5]!, property := ← handle a[3]!
        created := true } }
    | _ => throwError "Puddle printer: unsupported creation declaration{indentExpr decl}"
  -- Names follow handle allocation, including metadata produced by inspections.
  let mut types := 0
  let mut props := 0
  let mut metadata := #[]
  for item in d.metadata.qsort (fun a b => a.id < b.id) do
    let isType := item.name.startsWith "T"
    let name := if isType then s!"T{types}" else s!"P{props}"
    if isType then types := types + 1 else props := props + 1
    metadata := metadata.push { item with name }
  return { d with metadata }

private def metadataName (d : Description) (id : Nat) : String :=
  ((d.metadata.find? (·.id == id)).map (·.name)).getD s!"metadata#{id}"

private def leafName (index : Nat) : String :=
  if index < 3 then #["X", "Y", "Z"][index]! else s!"X{index}"

private def opName (d : Description) (op : Operation) : String :=
  d.names[op.id]?.getD <| if op.id == d.root then "root" else
    if #["llvm.mlir.constant", "arith.constant", "gmir.g_constant"].contains op.opcode then
      s!"C{d.operations.findIdx (·.id == op.id)}"
    else
      s!"{if op.created then "new" else "a"}{d.operations.findIdx (·.id == op.id)}"

private def valueName (d : Description) (id : Nat) : String :=
  match d.leaves.findIdx? (·.1 == id) with
  | some i => d.names[id]?.getD (leafName i)
  | none => match d.operations.find? (·.results.contains id) with
    | some op => opName d op ++ if op.results.size == 1 then "" else s!".{op.results.findIdx (· == id)}"
    | none => s!"value#{id}"

private def freshName (used : Std.HashSet String) (base : String) : String := Id.run do
  let mut candidate := base
  for i in [:used.size + 1] do
    if !used.contains candidate then return candidate
    candidate := s!"{base}_{i + 1}"
  return candidate

-- Graph references are strings, whereas symbolic parameters are printed by Lean.
-- Reserve the existing local names before introducing any of our own, including
-- metadata locals, so both parts of the output agree on distinct names.
private def nameHandles (d : Description) : MetaM Description := do
  let mut used : Std.HashSet String := {}
  for decl in ← getLCtx do
    used := used.insert decl.userName.eraseMacroScopes.toString
    used := used.insert (← ppExpr decl.toExpr).pretty
  let mut names := d.names
  for i in [:d.leaves.size] do
    let name := freshName used (leafName i)
    used := used.insert name
    names := names.insert d.leaves[i]!.1 name
  for op in d.operations do
    let name := freshName used (opName d op)
    used := used.insert name
    names := names.insert op.id name
  let mut metadata := #[]
  for item in d.metadata do
    let name := freshName used item.name
    used := used.insert name
    metadata := metadata.push { item with name }
  return { d with names, metadata }

private def tuple (values : Array String) : String :=
  if values.size == 1 then values[0]! else "(" ++ String.intercalate ", " values.toList ++ ")"

private def dialect (op : Operation) : String := (op.opcode.splitOn ".").head!

private def commonDialect (d : Description) : Option String := do
  let op ← d.operations[0]?
  let name := dialect op
  if d.operations.all (fun op => dialect op == name) then some name else none

private def application (d : Description) (op : Operation) (operands : Array String) : String := Id.run do
  if let some literal := op.literal then return literal
  let name := if (commonDialect d).isSome then
      String.intercalate "." ((op.opcode.splitOn ".").drop 1)
    else op.opcode
  let infixOp := match op.opcode with
    | "llvm.add" | "arith.addi" => some "+"
    | "llvm.sub" | "arith.subi" => some "-"
    | "llvm.mul" | "arith.muli" => some "*"
    | "llvm.and" | "arith.andi" => some "&"
    | "llvm.or" | "arith.ori" => some "|"
    | "llvm.xor" | "arith.xori" => some "^"
    | _ => none
  if (commonDialect d).isSome && operands.size == 2 then
    if let some symbol := infixOp then
      return s!"({operands[0]!} {symbol} {operands[1]!})"
  return name ++ "(" ++ String.intercalate ", " operands.toList ++ ")"

private def uses (d : Description) (id : Nat) : Nat :=
  d.operations.foldl (fun n op => n + op.operands.count id) (d.replacements.count id)

private def shared (d : Description) (op : Operation) : Bool :=
  op.results.size != 1 || op.results.any (fun id => uses d id > 1)

-- Types and properties are printed separately, so operations that differ only
-- in that metadata can have identical expressions. Keep their references named.
private def namedOperations (d : Description) : Array Nat := Id.run do
  let expressions := d.operations.map fun op =>
    application d op (op.operands.map (valueName d))
  let mut named := #[]
  for i in [:d.operations.size] do
    let op := d.operations[i]!
    if shared d op || expressions.count expressions[i]! > 1 then
      named := named.push op.id
  return named

private def valueText (d : Description) (named : Array Nat) (fuel : Nat) (id : Nat) : String :=
  match fuel with
  | 0 => valueName d id
  | fuel + 1 =>
    match d.operations.find? (·.results.contains id) with
    | some op =>
      if named.contains op.id then valueName d id
      else if #["llvm.mlir.constant", "arith.constant", "gmir.g_constant"].contains op.opcode &&
          op.literal.isNone then valueName d id
      else application d op (op.operands.map (valueText d named fuel))
    | none => valueName d id

private def clean (e : Expr) : MetaM Expr := do
  return (← dsimp (← zetaReduce e) (← Simp.mkContext { autoUnfold := false })).1

private def exprText (e : Expr) : MetaM String := do
  -- Kernel reduction exposes Int constructors, which the usual delaborator
  -- prints as `Int.ofNat 0` rather than a literal.
  if e.isAppOf ``Int.ofNat then
    if let some n ← getNatValue? e.getAppArgs.back! then return toString n
  if e.isAppOf ``Int.negSucc then
    if let some n ← getNatValue? e.getAppArgs.back! then return toString (-(Int.ofNat n + 1))
  if let some value ← getIntValue? e then return toString value
  return (← ppExpr (← instantiateMVars e)).pretty

private def literalText (e : Expr) : MetaM String := do
  let text ← exprText e
  -- A symbolic payload can be an arbitrary Lean expression. Only identifiers
  -- and integer numerals can be inserted into our expression syntax ungrouped.
  if e.isFVar || e.isConst || text.toInt?.isSome then return text
  return s!"({text})"

private partial def metadataValue (e : Expr) (bindings : Array (Nat × Expr)) : MetaM Expr := do
  let type ← whnf (← inferType e)
  if type.isConstOf ``Unit || type.isConstOf ``PUnit then return mkConst ``Unit.unit
  if type.isAppOf ``Prod then
    return ← mkAppM ``Prod.mk #[← metadataValue (.proj ``Prod 0 e) bindings,
      ← metadataValue (.proj ``Prod 1 e) bindings]
  let id ← handle e
  let some (_, value) := bindings.find? (·.1 == id)
    | throwError "Puddle printer: missing metadata handle {id}"
  return value

private def applyText (fn arg : Expr) : MetaM String := do
  -- Beta/zeta reduction substitutes readable names without unfolding arbitrary guards.
  exprText (← clean (mkApp (← whnf fn) arg).headBeta)

private def typeConstraint (fn arg : Expr) : MetaM String := do
  let body ← zetaReduce (mkApp (← whnf fn) arg).headBeta
  -- MatchProg.type wraps the author's predicate in a checked TypeAttr cast.
  if body.isAppOf ``Option.getD && body.getAppArgs.back!.isConstOf ``Bool.false then
    let mapped := body.getAppArgs[body.getAppArgs.size - 2]!
    if mapped.isAppOf ``Option.map then
      let args := mapped.getAppArgs
      let cast := args.back!
      unless cast.isAppOf ``TypeAttr.cast? && cast.getAppArgs[0]! == arg do
        return "require " ++ (← exprText body)
      let predicate := args[args.size - 2]!
      let type ← whnf (← inferType predicate)
      if let .forallE _ attr _ _ := type then
        return ← withLocalDeclD ((← getLCtx).getUnusedName `t) attr fun t => do
          let condition ← applyText predicate t
          let name ← exprText arg
          let binder ← exprText t
          let label := s!"{name} : {← exprText attr}"
          return if condition == "true" then label else s!"{label}, where {binder} = {name}: {condition}"
  return "require " ++ (← exprText body)

private def field (e : Expr) (structureName : Name) (index : Nat) : MetaM Expr :=
  whnf (.proj structureName index e)

private def createdLiteral (op : Operation) (value : Expr) : MetaM (Option String) := do
  let attr ← match op.opcode with
    | "arith.constant" => field value ``ArithConstantProperties 0
    | "gmir.g_constant" => field value ``GMIRConstantProperties 0
    | "llvm.mlir.constant" => do
      let payload ← field value ``LLVMConstantProperties 0
      unless payload.isAppOf ``LLVMConstantValue.integer do return none
      pure payload.getAppArgs.back!
    | _ => return none
  return some (← literalText (← clean (.proj ``IntegerAttr 0 attr)))

private def recognizeConstant (fn : Expr) (template : Name) : MetaM (Option String) :=
  withoutModifyingState do
    let value ← mkFreshExprMVar (mkConst ``Int)
    if ← isDefEq fn (mkApp (mkConst template) value) then
      let value ← instantiateMVars value
      if !value.hasMVar then return some (← literalText value)
    return none

private def literals (d : Description) : MetaM Description := do
  let mut d := d
  for decl in d.matchDecls do
    let decl ← whnf decl
    if decl.isAppOf ``MatchDecl.operation then
      let args := decl.getAppArgs
      let a := args.extract (args.size - 8) args.size
      let id ← handle a[5]!
      if let some i := d.operations.findIdx? (·.id == id) then
        let op := d.operations[i]!
        if op.opcode == "arith.constant" || op.opcode == "llvm.mlir.constant" then
          let literal ← if op.opcode == "arith.constant" then
              recognizeConstant a[3]! ``Templates.arithConstant
            else recognizeConstant a[3]! ``Templates.integerConstant
          d := { d with operations := d.operations.set! i { op with literal } }
    if decl.isAppOf ``MatchDecl.applyNative then
      let args := decl.getAppArgs
      if let some literal ← recognizeConstant args.back! ``Templates.bitConstant then
        let inputs ← metadataHandles args[args.size - 2]!
        if inputs.size == 2 then
          let propId := inputs[1]!.1
          for i in [:d.operations.size] do
            let op := d.operations[i]!
            if !op.created && op.opcode == "llvm.mlir.constant" && op.property == propId &&
                op.types == #[inputs[0]!.1] then
              d := { d with operations := d.operations.set! i { op with literal := some literal } }
  for decl in d.createDecls do
    let decl ← whnf decl
    if decl.isAppOf ``CreateDecl.property then
      let args := decl.getAppArgs
      let id ← handle args.back!
      for i in [:d.operations.size] do
        let op := d.operations[i]!
        if op.created && op.property == id then
          let literal ← createdLiteral op args[args.size - 2]!
          d := { d with operations := d.operations.set! i { op with literal } }
  return d

private def constraints (d : Description) (bindings : Array (Nat × Expr)) : MetaM (Array String) := do
  let mut lines := #[]
  for decl in d.matchDecls do
    let decl ← whnf decl
    let args := decl.getAppArgs
    match decl.getAppFn.constName? with
    | some ``MatchDecl.type =>
      let value ← metadataValue args.back! bindings
      lines := lines.push (← typeConstraint args[args.size - 2]! value)
    | some ``MatchDecl.operation =>
      let a := args.extract (args.size - 8) args.size
      let value ← metadataValue a[4]! bindings
      let text ← applyText a[3]! value
      if text != "true" then lines := lines.push s!"require {text}"
    | some ``MatchDecl.applyNative =>
      lines := lines.push s!"require {← applyText args.back! (← metadataValue args[args.size - 2]! bindings)}"
    | some ``MatchDecl.inspectOperation =>
      let opId ← handle args[args.size - 3]!
      let op := (d.operations.find? (·.id == opId)).map (opName d) |>.getD s!"op#{opId}"
      let outputs ← metadataValue args.back! bindings
      lines := lines.push s!"{← exprText outputs} ← inspect {op} using {← exprText (← whnf args[args.size - 2]!)}"
    | _ => pure ()
  for decl in d.createDecls do
    let decl ← whnf decl
    let args := decl.getAppArgs
    match decl.getAppFn.constName? with
    | some ``CreateDecl.type | some ``CreateDecl.property =>
      let value := args[args.size - 2]!
      let value ← if decl.isAppOf ``CreateDecl.property then
          if value.hasFVar then clean (← whnf value) else reduce value
        else pure value
      lines := lines.push s!"{metadataName d (← handle args.back!)} = {← exprText value}"
    | some ``CreateDecl.applyNative =>
      let outputs ← metadataValue args.back! bindings
      let inputs ← metadataValue args[args.size - 3]! bindings
      lines := lines.push s!"{← exprText outputs} ← {← applyText args[args.size - 2]! inputs}"
    | _ => pure ()
  return lines

private def render (d : Description) (bindings : Array (Nat × Expr)) : MetaM Format := do
  let d ← literals d
  let some root := d.operations.find? (·.id == d.root)
    | throwError "Puddle printer: the matcher has no root operation declaration"
  let text := valueText d (namedOperations d) (d.operations.size + 1)
  let lhs := application d root (root.operands.map text)
  let rhs := tuple (d.replacements.map text)
  let heading := (commonDialect d).map (· ++ ": ") |>.getD ""
  let mut lines := #[s!"{heading}{lhs}  =>  {rhs}"]
  for op in d.operations do
    -- The detail graph always identifies the exact operands, even when the
    -- summary can inline them into a more readable expression.
    -- A bare literal carries no dialect. Preserve its opcode in mixed-dialect
    -- detail graphs, even when the summary uses the shorter literal notation.
    let expr := match op.literal with
      | some literal => if (commonDialect d).isNone then s!"{op.opcode}({literal})"
          else application d op (op.operands.map (valueName d))
      | none => application d op (op.operands.map (valueName d))
    let types := tuple (op.types.map (metadataName d))
    -- Also name inlined operations here, so property and inspection references are unambiguous.
    lines := lines.push s!"{opName d op} = {expr} : {types}{if op.created then " [created]" else ""}"
    lines := lines.push s!"{metadataName d op.property} = properties({opName d op})"
  for (id, type) in d.leaves do
    lines := lines.push s!"{valueName d id} : {metadataName d type}"
  lines := lines ++ (← constraints d bindings)
  let header := Format.text lines[0]!
  let detailLines := (lines.toList.drop 1).flatMap (·.splitOn "\n")
  let details := Format.joinSep (detailLines.map Format.text) Format.line
  return header ++ Format.line ++ "where" ++ Format.nest 2 (Format.line ++ details)

private def withMetadata (d : Description) (remaining : List Metadata)
    (bindings : Array (Nat × Expr)) : MetaM Format :=
  match remaining with
  | [] => render d bindings
  | item :: rest => withLocalDeclD (.mkSimple item.name) item.type fun value =>
    withMetadata d rest (bindings.push (item.id, value))

/-- Format an elaborated Puddle pattern, retaining Lean expressions for native conditions.
Parameters controlling graph construction (e.g. commutation flags) must be instantiated.
Parameters occurring only in predicates may remain symbolic. -/
def format (rule : Expr) : MetaM Format := withTransparency .all do
  let d ← nameHandles (← describe rule)
  withMetadata d d.metadata.toList #[]

end PrettyPrinter

/-- Print an instantiated Puddle rewrite in a human-readable, non-serialized notation. -/
elab "#print_puddle " rule:term : command => runTermElabM fun _ => do
  let expected ← mkAppM ``Pattern #[mkConst ``OpCode]
  let rule ← Term.elabTermAndSynthesize rule (some expected)
  logInfo (← PrettyPrinter.format (← instantiateMVars rule))

end
end Veir.Puddle
