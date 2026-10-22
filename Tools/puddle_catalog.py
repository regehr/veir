#!/usr/bin/env python3
"""Rebuild the Puddle Markdown/PDF catalog from a VeIR checkout.

Requires Python 3.9+, Lake with the checkout's Lean toolchain, Pandoc with its
Typst writer, and Typst. No Python packages are needed. The checkout must include
Veir.PatternRewriter.Puddle.PrettyPrinter. See --help and docs/puddle-printing.md.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from datetime import date
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
from urllib.parse import quote
import xml.etree.ElementTree as ET


PRINTER = "Veir.PatternRewriter.Puddle.PrettyPrinter"
EXECUTION = "Veir.PatternRewriter.Puddle.Execution"
# These families have graph-dependent opcode/arity parameters. Their concrete
# instances come from compiled patterns, named aliases, and pass_instances().
SPECIALIZED_FAMILIES = (
    "lowerStore", "lowerByteBinaryW", "lowerAshr", "lowerRotate",
    "lowerFshrGeneral", "lowerUnary", "lowerGetelementptr", "customLegalizeWord",
    "lowerExt", "lowerBswap", "lowerLoad", "lowerBinop", "lowerUnaryByteOp",
    "lowerRegCast", "widenTypeGroup", "gmirIcmp_pattern", "lowerFshConst",
    "sextw_signExtendingOpW_pattern", "lowerBitreverse", "lowerIntegerCast",
    "lowerIcmp", "lowerFshlGeneral", "lowerBinary", "drop_ext_low_word_pattern",
    "lowerLifetime",
)

# Elaborate existing definitions; Python never parses or reimplements rewrites.
# The normalization rules mirror unfoldPuddleBuilder, and the actual rendering
# is delegated to Veir.Puddle.PrettyPrinter.format. Special sampling policies in
# catalogExpand concern graph shape; scalar parameters stay symbolic.
LEAN_CORE = r'''
open Lean Meta Elab Command
set_option maxRecDepth 10000
set_option maxHeartbeats 0

meta def catalogContext : MetaM Simp.Context := do
  let mut thms : SimpTheorems := {}
  for n in #[``Veir.Puddle.Pattern.Builder,
      ``Veir.Puddle.MatchProg.build,
      ``Veir.Puddle.CreateProg.build,
      ``bind,
      ``pure,
      ``Veir.Puddle.MatchProg.value,
      ``Veir.Puddle.MatchProg.type,
      ``Veir.Puddle.MatchProg.root,
      ``Veir.Puddle.MatchProg.operation,
      ``Veir.Puddle.MatchProg.matchNative,
      ``Veir.Puddle.MatchProg.inspectOperation,
      ``Veir.Puddle.CreateProg.type,
      ``Veir.Puddle.CreateProg.operation,
      ``Veir.Puddle.CreateProg.property,
      ``Veir.Puddle.CreateProg.applyNative,
      ``Veir.Puddle.MetadataTuple.fresh,
      ``Veir.Puddle.IsMetadataTuple.shape_unit,
      ``Veir.Puddle.IsMetadataTuple.shape_type,
      ``Veir.Puddle.IsMetadataTuple.shape_property,
      ``Veir.Puddle.IsMetadataTuple.shape_type_cons,
      ``Veir.Puddle.IsMetadataTuple.shape_property_cons,
      ``Veir.Puddle.MetadataTuple.Shape.fresh,
      ``Veir.Puddle.MetadataTuple.Atom.fresh,
      ``Nat.zero_add,
      ``List.size_toArray,
      ``List.length_cons,
      ``List.length_nil,
      ``Array.size_map,
      ``Array.size_range,
      ``Nat.lt_add_one,
      ``getElem!_pos,
      ``Array.getElem_map,
      ``Array.getElem_range,
      ``Nat.add_zero,
      ``List.cons_append,
      ``List.nil_append,
      ``List.reverse_cons,
      ``List.reverse_nil] do
    if ← isProp (← getConstInfo n).type then
      thms ← thms.addConst n
    else
      thms ← thms.addDeclToUnfold n

  for (name, ci) in (← getEnv).constants.toList do
    let .defnInfo info := ci | continue
    unless info.safety == .safe do continue
    unless (← findDeclarationRanges? name).isSome do continue
    let body := info.type.getForallBody
    if [``Veir.Puddle.Pattern,
      ``Veir.Puddle.MatchProg.Builder,
      ``Veir.Puddle.CreateProg.Builder].any body.isAppOf then
      thms ← thms.addDeclToUnfold name
  Simp.mkContext { maxSteps := 1000000 } (simpTheorems := #[thms])

meta partial def catalogFamilies (e : Expr) (seen : NameSet := {}) : MetaM NameSet := do
  let mut found := seen
  for n in e.getUsedConstants do
    if found.contains n then continue
    let some (.defnInfo info) := (← getEnv).find? n | continue
    unless info.type.getForallBody.isAppOf ``Veir.Puddle.Pattern do continue
    if n == ``Veir.Puddle.Pattern.Builder then continue
    found := found.insert n
    found ← catalogFamilies info.value found
  return found

meta def catalogRecord (ctx : Simp.Context) (out : IO.FS.Handle) (name : Name) (rule : Expr)
    (params : Array String) : MetaM Unit := do
  let env ← getEnv
  let mod := (env.getModuleIdxFor? name).map (env.header.moduleNames[·]!) |>.getD .anonymous
  let line := (← findDeclarationRanges? name).map (·.selectionRange.pos.line) |>.getD 0
  let mut fields := [("kind", toJson "rendering"), ("name", toJson name.toString), ("module", toJson mod.toString),
    ("line", toJson line), ("parameters", toJson params),
    ("expression", toJson (← ppExpr rule).pretty),
    ("families", toJson ((← catalogFamilies rule).toArray.map Name.toString))]
  try
    let printed ← withTheReader Core.Context (fun c => { c with maxHeartbeats := 500000000 }) <| withCurrHeartbeats do
      let (normalized, _) ← simp rule ctx
      Veir.Puddle.PrettyPrinter.format normalized.expr
    fields := fields ++ [("output", toJson (printed.pretty 100))]
  catch ex =>
    let msg ← ex.toMessageData.toString
    fields := fields ++ [("error", toJson (String.ofList (msg.toList.take 1200)))]
  out.putStrLn (Json.mkObj fields).compress
  out.flush

meta partial def catalogExpand (ctx : Simp.Context) (out : IO.FS.Handle) (name : Name) (fn ty : Expr)
    (params : Array String := #[]) : MetaM Unit := do
  let ty ← whnf ty
  if let .forallE n domain body _ := ty then
    let d ← whnf domain
    if d.isConst && d.constName!.getString! == "ScalarLiteral" then
      withLocalDeclD (n.appendAfter "_value") (mkConst ``Int) fun c => do
        let integers := if name.getString! == "IS5122" && n == `cond then
            #[toExpr (0 : Int), toExpr (1 : Int)] else #[c]
        let choices := integers.map (mkApp (mkConst (d.constName! ++ `integer))) ++
            #[mkConst (d.constName! ++ `zero), mkConst (d.constName! ++ `poison)]
        for arg in choices do
          catalogExpand ctx out name (mkApp fn arg) (body.instantiate1 arg)
            (params.push s!"{n} = {(← ppExpr arg).pretty}; {n}_value : Int when used")
      return
    let mut choices : Array Expr := #[]
    if d.isConstOf ``Bool then
      choices := #[mkConst ``Bool.false, mkConst ``Bool.true]
    else if d.isConst && ["MinMaxKind", "ScaledCmpShape", "PowerShiftSafety"].contains d.constName!.getString! then
      if let .inductInfo info ← getConstInfo d.constName! then
        choices := info.ctors.toArray.map mkConst
    else if n == `n && (["gepPoisonBaseFamily", "gepPoisonBaseCore"].contains name.getString!) then
      choices := #[mkNatLit 0, mkNatLit 1, mkNatLit 2, mkNatLit 3]
    else if name.getString! == "gepPoisonIndexFamily" then
      choices := #[mkNatLit 0, mkNatLit 1, mkNatLit 2]
    else if d.isConst && d.constName!.getString! == "GEPPoisonCause" then
      for n in [0,1,2,3] do
        choices := choices.push (mkApp (mkConst (d.constName! ++ `base)) (mkNatLit n))
      for before in [0,1,2] do
        for after in [0,1,2] do
          choices := choices.push (mkAppN (mkConst (d.constName! ++ `index)) #[mkNatLit before, mkNatLit after])
    if !choices.isEmpty then
      for arg in choices do
        catalogExpand ctx out name (mkApp fn arg) (body.instantiate1 arg)
          (params.push s!"{n} = {(← ppExpr arg).pretty}")
    else if d.isAppOf ``List && d.getAppArgs.back!.isConstOf ``Int then
      withLocalDeclD `a (mkConst ``Int) fun a =>
        withLocalDeclD `b (mkConst ``Int) fun b => do
          for args in #[#[], #[a], #[a,b]] do
            let arg ← mkListLit (mkConst ``Int) args.toList
            catalogExpand ctx out name (mkApp fn arg) (body.instantiate1 arg)
              (params.push s!"{n} = {(← ppExpr arg).pretty}; representative length {args.size}, a b : Int")
    else
      withLocalDeclD n domain fun arg => do
        catalogExpand ctx out name (mkApp fn arg) (body.instantiate1 arg)
          (params.push s!"{n} : {(← ppExpr domain).pretty}")
  else
    catalogRecord ctx out name fn params

'''

LEAN_RUNNER = r'''
meta def catalogIsProduction (env : Environment) (name : Name) : Bool := Id.run do
  let some idx := env.getModuleIdxFor? name | return false
  let mod := env.header.moduleNames[idx]!.toString
  return mod.startsWith "Veir." && !mod.startsWith "Veir.PatternRewriter."

meta partial def compiledRule? (e : Expr) (fuel : Nat := 3) : MetaM (Option Expr) := do
  if let some app := e.find? (fun x => x.isAppOf ``Veir.Puddle.Pattern.compile && !x.hasLooseBVars) then
    return some app.getAppArgs.back!
  if fuel == 0 then return none
  if let some unfolded ← unfoldDefinition? e then
    return ← compiledRule? unfolded (fuel - 1)
  return none

run_cmd runTermElabM fun _ => do
  let env ← getEnv
  let ctx ← catalogContext
  let out ← IO.FS.Handle.mk __OUTPUT__ .write
  let constants := env.constants.toList.mergeSort (fun a b => a.1.toString < b.1.toString)
  let mut names : Array Name := #[]
  for (name, ci) in constants do
    unless catalogIsProduction env name do continue
    let .defnInfo info := ci | continue
    unless info.safety == .safe do continue
    unless info.type.getForallBody.isAppOf ``Veir.Puddle.Pattern do continue
    unless info.type.getForallBody.getAppArgs[0]!.isConstOf ``Veir.OpCode do continue
    let some range ← findDeclarationRanges? name | continue
    let mod := env.header.moduleNames[(env.getModuleIdxFor? name).get!]!
    let kind := if (info.value.find? (·.isConstOf ``Veir.Puddle.Pattern.Builder)).isSome then "builder"
      else if (info.value.find? (·.isConstOf ``Veir.Puddle.Pattern.mk)).isSome then "record"
      else "alias"
    out.putStrLn (Json.mkObj [("kind", toJson "definition"), ("name", toJson name.toString),
      ("module", toJson mod.toString), ("line", toJson range.selectionRange.pos.line),
      ("construction", toJson kind)]).compress
    if info.type.isAppOf ``Veir.Puddle.Pattern then
      names := names.push name
      catalogRecord ctx out name (mkConst name) #[]
    else if !__SPECIALIZED_FAMILIES__.contains name.getString! then
      catalogExpand ctx out name (mkConst name) info.type
  for (name, ci) in constants do
    unless catalogIsProduction env name do continue
    let .defnInfo info := ci | continue
    let value := info.value
    let head := value.getAppFn.constName?.getD .anonymous
    -- Ordinary function bodies have no constant head. Do not call getString!
    -- on the anonymous fallback (or on a numeric name component).
    let headName := match head with | .str _ last => last | _ => ""
    unless info.type.isAppOf ``Veir.Puddle.CompiledPattern ||
        ["drop_ext_low_word", "sextw_signExtendingOpW"].contains headName do continue
    unless (← findDeclarationRanges? name).isSome do continue
    if headName == "drop_ext_low_word" then
      let args := value.getAppArgs
      let some arity ← getNatValue? args[2]! | continue
      let family := head.getPrefix ++ `drop_ext_low_word_pattern
      for index in [:arity] do
        let rule := mkAppN (mkConst family) #[args[0]!, args[1]!, args[2]!, mkNatLit index, args[3]!]
        catalogRecord ctx out name rule #[s!"index = {index}"]
    else if info.type.isAppOf ``Veir.Puddle.CompiledPattern || headName == "sextw_signExtendingOpW" then
      let some rule ← compiledRule? value | continue
      if names.contains (rule.getAppFn.constName?.getD .anonymous) then continue
      catalogRecord ctx out name rule #[]
  withLocalDeclD `width (mkConst ``Nat) fun _ => do
    let width := mkIdent `width
    let entries ← (__INSTANCES__ : Array (TermElabM (TSyntax `term))).mapM id
    for stx in entries do
      let expected ← mkAppM ``Veir.Puddle.Pattern #[mkConst ``Veir.OpCode]
      let rule ← Term.elabTermAndSynthesize stx (some expected)
      let rule ← instantiateMVars rule
      catalogRecord ctx out rule.getAppFn.constName! rule
        #[s!"{(← ppExpr rule).pretty}; width : Nat when used"]
'''

PDF_TEMPLATE = r'''
#set document(title: "Puddle rewrite catalog")
#set page(
  paper: "us-letter",
  margin: (left: 0.6in, right: 0.6in, top: 0.65in, bottom: 0.65in),
  numbering: "1",
  number-align: center,
  header: align(right, text(size: 7pt, fill: rgb("666666"))[VeIR · Puddle rewrite catalog]),
)
#set text(font: __TEXT_FONTS__, size: 9pt)
#set par(justify: false, leading: 0.45em, spacing: 0.65em)
#set heading(numbering: none)
#show heading.where(level: 1): set text(size: 22pt)
#show heading.where(level: 2): set text(size: 15pt, fill: rgb("233c58"))
#show heading.where(level: 3): set text(size: 11pt, fill: rgb("233c58"))
#show heading.where(level: 4): set text(size: 9pt)
#show link: set text(fill: rgb("245a88"))
#show raw: set text(font: __CODE_FONTS__, size: 7.5pt)
#show raw.where(block: true): it => {
  let parts = it.text.split("\nwhere\n")
  let body = if parts.len() == 2 {
    [
      #block(above: 0pt, below: 0pt)[
        #show raw: set text(size: 11pt, weight: "semibold")
        #raw(parts.at(0).trim())
      ]
      #v(12pt)
      #raw("where\n" + parts.at(1))
    ]
  } else { it }
  block(width: 100%, inset: 6pt, fill: rgb("f5f6f8"), radius: 2pt,
    breakable: true, body)
}
#set table(inset: 4pt, stroke: (bottom: 0.3pt + rgb("dddddd")))
$body$
'''


class CatalogError(Exception):
    """An actionable generation failure, without a Python traceback."""


def lean_code(source: str) -> str:
    """Remove nested Lean comments and string contents, preserving newlines."""
    result = []
    i, depth = 0, 0
    while i < len(source):
        pair = source[i:i + 2]
        if depth:
            if pair == '/-':
                depth += 1
                i += 2
            elif pair == '-/':
                depth -= 1
                i += 2
            else:
                result.append('\n' if source[i] == '\n' else ' ')
                i += 1
        elif pair == '/-':
            result.append(' ')
            depth = 1
            i += 2
        elif pair == '--':
            end = source.find('\n', i)
            i = len(source) if end == -1 else end
        elif source[i] == '"':
            result.append(' ')
            i += 1
            while i < len(source):
                if source[i] == '\\':
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    result.append('\n' if source[i] == '\n' else ' ')
                    i += 1
        else:
            result.append(source[i])
            i += 1
    return ''.join(result)


def discover_modules(repo: Path) -> dict[str, bool]:
    """Find candidate source modules; Lean performs the declaration inventory.

    Include reverse-importing definitions to catch aliases with inferred types.
    False positives are harmless: only Pattern OpCode definitions are exported.
    """
    sources = {}
    for path in sorted((repo / 'Veir').rglob('*.lean')):
        name = '.'.join(path.relative_to(repo).with_suffix('').parts)
        if name.startswith('Veir.PatternRewriter.'):
            continue
        code = lean_code(path.read_text(encoding='utf-8'))
        imports = set(re.findall(
            r'^\s*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?([\w.]+)', code, re.M))
        body = re.sub(r'^\s*(?:(?:public|meta)\s+)*import\b[^\n]*', '', code, flags=re.M)
        sources[name] = (body, imports, bool(re.match(r'\s*module\b', code)))
    selected = {name for name, (body, _, _) in sources.items()
                if re.search(r'\bPattern\b', body)}
    while True:
        # Follow re-export-only modules too: an inferred alias may import a
        # barrel module rather than the file containing its builder.
        additions = {name for name, (_, imports, _) in sources.items() if imports & selected}
        if additions <= selected:
            break
        selected |= additions
    if not selected:
        raise CatalogError('No candidate Puddle pattern modules found under Veir/.')
    return {name: sources[name][2] for name in sorted(selected)}


def pass_instances(modules: set[str]) -> list[str]:
    """Graph-dependent cases registered by the current passes.

    These are inputs to Lean's existing builders, not hand-written rewrites.
    Missing declarations or new unsupported families fail the coverage check.
    """
    terms = []
    if 'Veir.Passes.InstructionSelection.RISCV64' in modules:
        for function, ops in [('lowerLoad', ['lb', 'lh', 'lw', 'ld']),
                              ('lowerStore', ['sb', 'sh', 'sw', 'sd'])]:
            for folded in ['false', 'true']:
                for width, op in zip([1, 2, 4, 8], ops):
                    terms.append(f'Veir.{function} {folded} {width} .{op}')
        terms.extend(f'Veir.lowerGetelementptr {scale}' for scale in [1, 2, 4, 8])
        for pred in ['eq', 'ne', 'slt', 'sgt', 'ult', 'ugt', 'sge', 'sle', 'uge', 'ule']:
            for zero in (['false', 'true'] if pred in ['eq', 'ne'] else ['false']):
                terms.append(f'Veir.gmirIcmp_pattern .{pred} {zero}')
                terms.extend(f'Veir.lowerIcmp (.llvm .icmp) .{pred} {width} {zero}'
                             for width in [8, 32, 64])
    if 'Veir.Passes.Legalization.RISCV64LegalizerInfo' in modules:
        for op, rv in [('add', 'addw'), ('sub', 'subw'), ('mul', 'mulw'),
                       ('sdiv', 'divw'), ('udiv', 'divuw'), ('urem', 'remuw')]:
            terms.append(f'Veir.customLegalizeWord .g_{op} .{rv} ()')
    if 'Veir.Passes.Legalization.LegalizerHelper' in modules:
        for op, group, ext in [
            ('add', 0, 'anyext'), ('sub', 0, 'anyext'), ('icmp', 0, 'anyext'),
            ('icmp', 1, 'sext'), ('and', 0, 'anyext'), ('or', 0, 'anyext'),
            ('xor', 0, 'anyext'), ('mul', 0, 'anyext'), ('sdiv', 0, 'sext'),
            ('srem', 0, 'sext'), ('udiv', 0, 'zext'), ('urem', 0, 'zext'),
        ]:
            update = ' Veir.clearNswNuwProperties' if op in ['add', 'sub', 'mul'] else ''
            terms.append(f'Veir.widenTypeGroup .g_{op} (.type {group}) '
                         f'.g_{ext} $width:ident{update}')
    return terms


def make_driver(modules: list[str], modern: bool, output: Path) -> str:
    # Legacy InstSimplify modules cannot be imported by a module-system driver.
    # Modern pass definitions need `import all` to expose their private builders.
    imports = ['module'] if modern else []
    imports.append(f'import {PRINTER}')
    imports.append(f'import {EXECUTION}')
    if modern:
        imports.append('import all Veir.Dialects.GMIR.OpInfo')
    imports.extend(f'import {"all " if modern else ""}{module}' for module in modules)
    entries = '#[' + ',\n      '.join(f'`(term| {term})' for term in pass_instances(set(modules))) + ']'
    runner = LEAN_RUNNER.replace('__OUTPUT__', json.dumps(str(output), ensure_ascii=False))
    runner = runner.replace('__SPECIALIZED_FAMILIES__', '#[' + ', '.join(
        json.dumps(name) for name in SPECIALIZED_FAMILIES) + ']')
    runner = runner.replace('__INSTANCES__', entries)
    return '\n'.join(imports) + '\n' + LEAN_CORE + runner


def run(command: list[str], repo: Path, log: Path, stage: str) -> None:
    """Use argument arrays throughout; paths and Lean terms never enter a shell."""
    print(f'{stage} (log: {log})', flush=True)
    with log.open('w', encoding='utf-8') as handle:
        process = subprocess.Popen(command, cwd=repo, stdout=handle, stderr=subprocess.STDOUT)
        try:
            while True:
                try:
                    status = process.wait(timeout=30)
                    break
                except subprocess.TimeoutExpired:
                    print(f'  Still {stage.lower()}...', flush=True)
        except BaseException:
            process.terminate()
            try:
                process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()
            raise
    if status:
        tail = '\n'.join(log.read_text(encoding='utf-8', errors='replace').splitlines()[-20:])
        raise CatalogError(f'{stage} failed (exit {status}).\n{tail}\nFull log: {log}')


def collect_records(paths: list[Path]) -> tuple[list[dict], list[dict]]:
    definitions, renderings = {}, {}
    for path in paths:
        for number, line in enumerate(path.read_text(encoding='utf-8').splitlines(), 1):
            try:
                record = json.loads(line)
            except ValueError as error:
                raise CatalogError(f'Invalid Lean output at {path}:{number}: {error}') from error
            if record['kind'] == 'definition':
                definitions[record['name']] = record
            elif record['kind'] == 'rendering':
                key = (record['name'], record['expression'], tuple(record['parameters']))
                renderings[key] = record
            else:
                raise CatalogError(f'Unknown output record kind in {path}:{number}')
    return list(definitions.values()), list(renderings.values())


def validate_catalog(definitions: list[dict], records: list[dict]) -> None:
    if not definitions or not records:
        raise CatalogError('Lean exported an empty catalog.')
    errors = [r for r in records if 'error' in r]
    if errors:
        details = '\n'.join(f"  {r['name']}: {r['error'][:300]}" for r in errors[:10])
        raise CatalogError(f'{len(errors)} pattern renderings failed:\n{details}\n'
                           'Extend the graph-parameter policy in catalogExpand or pass_instances().')
    covered = {r['name'] for r in records} | {n for r in records for n in r['families']}
    missing = sorted(d['name'] for d in definitions if d['name'] not in covered)
    if missing:
        raise CatalogError('Uncovered pattern declarations:\n  ' + '\n  '.join(missing) +
                           '\nAdd their graph-parameter instances to the script.')
    for record in records:
        output = record['output']
        if '  =>  ' not in output or '\nwhere\n' not in output:
            raise CatalogError(f"Incomplete rendering: {record['name']}")
        if re.search(r'\?(?:m|u)\.[0-9]|sorryAx|metadata#[0-9]|value#[0-9]', output):
            raise CatalogError(f"Unresolved term or handle in {record['name']}")


def display(name: str) -> str:
    return re.sub(r'^_private\..*?\.[0-9]+\.', '', name)


def slug(name: str) -> str:
    return re.sub(r'[^a-z0-9]+', '-', name.lower()).strip('-')


def parameters(items: list[str]) -> str:
    result = []
    for item in items:
        item = re.sub(r'Veir\.InstSimplify\.(?:MinMaxKind|ScaledCmpShape|PowerShiftSafety|'
                      r'GEPPoisonCause|ScalarLiteral)\.', '.', item)
        item = re.sub(r'; (\w+_value) : Int when used', lambda m:
                      ', ' + m[1] + ' : Int' if m[1] in item[:m.start()] else '', item)
        item = item.replace('; width : Nat when used', '; width : Nat'
                            if re.search(r'\bwidth\b', item.split(';')[0]) else '')
        result.append(item)
    return '; '.join(result)


def git_value(repo: Path, *args: str) -> str:
    try:
        result = subprocess.run(['git', *args], cwd=repo, capture_output=True, text=True)
        return result.stdout.strip() if result.returncode == 0 else 'unknown'
    except FileNotFoundError:
        return 'unknown'


def markdown(repo: Path, output: Path, definitions: list[dict], records: list[dict]) -> str:
    def source(module: str, line: int = 0) -> str:
        path = repo / (module.replace('.', '/') + '.lean')
        if not path.is_file():
            raise CatalogError(f'Declaration source does not exist: {path}')
        relative = quote(Path(os.path.relpath(path, output.parent)).as_posix(), safe='/')
        return relative + (f'#L{line}' if line else '')

    def area(module: str) -> str:
        for prefix, title in [
            ('Veir.InstSimplify.', 'InstSimplify'),
            ('Veir.Passes.InstructionSelection.', 'RISC-V instruction selection'),
            ('Veir.Passes.LLVMToGMIR', 'LLVM to GMIR'),
            ('Veir.Passes.Legalization.', 'Legalization'),
            ('Veir.Passes.RISCVCombines.', 'RISC-V combines'),
        ]:
            if module.startswith(prefix):
                return title
        return 'Other production patterns'

    kinds = Counter(d['construction'] for d in definitions)
    areas = list(dict.fromkeys(area(d['module']) for d in sorted(definitions, key=lambda d: d['module'])))
    revision = git_value(repo, 'rev-parse', 'HEAD')
    branch = git_value(repo, 'branch', '--show-current') or 'detached HEAD'
    lines = [
        '# Puddle rewrite catalog', '',
        f'Generated on {date.today().isoformat()} from the working tree at `{revision}` (`{branch}`).', '',
        f'**{len(records):,} renderings**, covering all **{len(definitions):,} discovered production '
        f'`Pattern OpCode` declarations** under `Veir/`: {kinds["builder"]} builder definitions, '
        f'{kinds["record"]} direct record definitions, and {kinds["alias"]} aliases or dispatchers. '
        'The renderings also include concrete instances extracted from compiled pass patterns. '
        'Generic builders are covered through the displayed instances; compiler-generated auxiliary '
        'declarations and unit tests are excluded.', '',
        f'The output comes from the Lean [Puddle pretty printer]({source(PRINTER)}), after simplifying '
        'builder state with the rules used by `unfoldPuddleBuilder`. Every rendering retains the '
        'complete `where` block, including types, properties, guards, and native computations. '
        'This is reading notation, not an input format.', '',
        '## Parameter coverage', '',
        '- Scalar parameters remain symbolic when they do not determine graph structure. '
        'Boolean graph choices and the supported finite opcode/shape selectors are expanded.',
        '- Scalar-literal families cover integer, zero-marker, and poison constructors. For `IS5122`, '
        'integer conditions use `0` and `1` to represent the two possible i1 values; selected integer '
        'payloads remain symbolic.',
        '- Unbounded GEP families use representative graph sizes: 0–3 dynamic indices, 0–2 zero-index '
        'payloads, and 0–2 dynamic indices on each side of a poison index. These samples do not '
        'enumerate every arity. The two `Core` definitions are direct-record versions of builder '
        'families and are included too.',
        '- Generic pass helpers use their concrete pass instances. Comparison lowering includes its '
        'supported 8-, 32-, and 64-bit forms; widening keeps the target width symbolic. Arbitrary '
        'combinations of opcode/helper parameters are not enumerated.', '',
        '## Coverage', '',
        '| Area | Builder definitions | Other Pattern declarations | Renderings |',
        '| --- | ---: | ---: | ---: |',
    ]
    for title in areas:
        ds = [d for d in definitions if area(d['module']) == title]
        rs = [r for r in records if area(r['module']) == title]
        builders = sum(d['construction'] == 'builder' for d in ds)
        lines.append(f'| [{title}](#{slug(title)}) | {builders} | {len(ds)-builders} | {len(rs):,} |')
    lines += [f'| **Total** | **{kinds["builder"]}** | **{len(definitions)-kinds["builder"]}** '
              f'| **{len(records):,}** |', '',
              'Coverage was checked against the elaborated Lean declarations: no discovered production '
              'pattern declaration is omitted, and no rendering failed.', '', '## Module index', '',
              '| Module | Renderings |', '| --- | ---: |']
    by_module = defaultdict(list)
    for record in records:
        by_module[record['module']].append(record)
    for module in sorted(by_module):
        lines.append(f'| [{module}](#module-{slug(module)}) | {len(by_module[module])} |')
    lines.append('')
    defined = {d['name'] for d in definitions}
    builders = {d['name'] for d in definitions if d['construction'] == 'builder'}
    for title in areas:
        lines += [f'## {title}', '']
        for module in sorted(m for m in by_module if area(m) == title):
            lines += [f'<a id="module-{slug(module)}"></a>', '', f'### {module}', '',
                      f'[Source module]({source(module)})', '']
            grouped = defaultdict(list)
            for record in by_module[module]:
                grouped[record['name']].append(record)
            for name, variants in sorted(grouped.items(), key=lambda kv:
                                         (min(r['line'] for r in kv[1]), display(kv[0]))):
                lines += [f'#### {display(name)}', '',
                          f'[Source]({source(module, variants[0]["line"])})', '']
                families = sorted({n for r in variants for n in r['families'] if n in builders and n != name})
                if families:
                    lines += ['Builder families: ' + ', '.join(f'`{display(n)}`' for n in families) + '.', '']
                for index, record in enumerate(variants, 1):
                    if record['parameters']:
                        label = f'Variant {index}' if len(variants) > 1 else 'Parameters'
                        lines += [f'**{label}:** `{parameters(record["parameters"])}`', '']
                    elif name not in defined:
                        lines += ['**Pattern expression:**', '', '```text', record['expression'], '```', '']
                    lines += ['```text', record['output'], '```', '']
    return '\n'.join(lines)


def fonts(typst: str, requested: str | None, code: str | None) -> tuple[str, str, list[str]]:
    result = subprocess.run([typst, 'fonts'], check=True, capture_output=True, text=True)
    available = {line.strip() for line in result.stdout.splitlines()}

    def choose(explicit: str | None, candidates: list[str]) -> str:
        if explicit:
            if explicit not in available:
                raise CatalogError(f'Font {explicit!r} is unavailable; see `typst fonts`.')
            return explicit
        for candidate in candidates:
            if candidate in available:
                return candidate
        raise CatalogError('No suitable font found. Specify --font and --code-font; see `typst fonts`.')

    body = choose(requested, ['Helvetica Neue', 'Arial', 'DejaVu Sans', 'Libertinus Serif', 'New Computer Modern'])
    mono = choose(code, ['DejaVu Sans Mono', 'Menlo', 'Liberation Mono'])
    fallback = [f for f in ['Arial Unicode MS', 'Noto Sans Symbols 2'] if f in available]
    return body, mono, fallback


def verify_pdf_text(markdown_text: str, extracted: str) -> None:
    """Check every full code block, including those split across PDF pages."""
    pages = []
    for page in extracted.split('\f'):
        lines = [line for line in page.splitlines() if line.strip() != 'VeIR · Puddle rewrite catalog']
        while lines and not lines[-1].strip():
            lines.pop()
        if lines and re.fullmatch(r'\s*\d+\s*', lines[-1]):
            lines.pop()
        pages.append('\n'.join(lines))
    normalize = lambda s: re.sub(r'\s+', '', s)
    body = normalize('\n'.join(pages))
    blocks = re.findall(r'```text\n(.*?)\n```', markdown_text, re.S)
    for index, block in enumerate(blocks, 1):
        if normalize(block) not in body:
            raise CatalogError(f'PDF text verification failed for code block {index}: {block.splitlines()[0]}')
    expected = sum('\nwhere\n' in block for block in blocks)
    actual = sum(line.strip() == 'where' for line in extracted.splitlines())
    if actual != expected:
        raise CatalogError(f'PDF contains {actual} rewrite blocks; expected {expected}.')


def render_pdf(text: str, repo: Path, work: Path, tools: dict[str, str],
               body_font: str, code_font: str, fallback: list[str]) -> Path:
    # Raw HTML anchors vanish in Pandoc's Typst writer. Attach them to headings
    # so the module index remains clickable in both Markdown and PDF.
    pdf_markdown = re.sub(r'<a id="([^"]+)"></a>\s*\n### ([^\n]+)', r'### \2 {#\1}', text)
    (work / 'catalog.md').write_text(pdf_markdown, encoding='utf-8')
    font_tuple = lambda primary: '(' + ', '.join(json.dumps(f, ensure_ascii=False)
                                               for f in [primary, *fallback]) + ',)'
    template = PDF_TEMPLATE.replace('__TEXT_FONTS__', font_tuple(body_font))
    template = template.replace('__CODE_FONTS__', font_tuple(code_font))
    (work / 'template.typst').write_text(template, encoding='utf-8')
    run([tools['pandoc'], str(work / 'catalog.md'), '--from=markdown', '--to=typst',
         '--standalone', '--syntax-highlighting=none', f'--template={work / "template.typst"}',
         f'--output={work / "catalog.typ"}'], repo, work / 'pandoc.log', 'Converting Markdown')
    pdf = work / 'catalog.pdf'
    run([tools['typst'], 'compile', str(work / 'catalog.typ'), str(pdf)],
        repo, work / 'typst.log', 'Rendering PDF')
    if not pdf.read_bytes().startswith(b'%PDF-'):
        raise CatalogError(f'Typst did not produce a PDF: {pdf}')
    extractor = shutil.which('pdftotext')
    if extractor:
        extracted = work / 'extracted.txt'
        run([extractor, '-layout', str(pdf), str(extracted)], repo, work / 'pdf-text.log', 'Checking PDF text')
        verify_pdf_text(text, extracted.read_text(encoding='utf-8'))
        bounds = work / 'bounds.html'
        run([extractor, '-bbox', str(pdf), str(bounds)], repo, work / 'pdf-bounds.log', 'Checking page margins')
        ns = {'p': 'http://www.w3.org/1999/xhtml'}
        for page_number, page in enumerate(ET.parse(bounds).findall('.//p:page', ns), 1):
            for word in page.findall('.//p:word', ns):
                if float(word.attrib['xMin']) < 30 or float(word.attrib['xMax']) > float(page.attrib['width']) - 30:
                    raise CatalogError(f'Text exceeds the PDF margins on page {page_number}: {word.text}')
    else:
        print('pdftotext not found; skipping PDF text/bounds verification.', flush=True)
    return pdf


def publish(source: Path, destination: Path) -> None:
    """Replace an output only after generation and validation have succeeded."""
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=destination.parent, prefix='.' + destination.name,
                                     delete=False) as handle:
        temporary = Path(handle.name)
    try:
        shutil.copyfile(source, temporary)
        os.replace(temporary, destination)
    finally:
        temporary.unlink(missing_ok=True)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('repo', nargs='?', type=Path, default=Path.cwd(), help='VeIR checkout (default: current directory)')
    parser.add_argument('-o', '--output', type=Path, help='PDF path, relative to the current directory; default: REPO/docs/puddle-patterns.pdf')
    parser.add_argument('--skip-build', action='store_true', help='use existing Lean build products (must be current)')
    parser.add_argument('--work-dir', type=Path, help='parent for per-run logs/intermediates; default: REPO/.lake/puddle-catalog')
    parser.add_argument('--font', help='body font (default: choose an installed font)')
    parser.add_argument('--code-font', help='monospace font (default: choose an installed font)')
    args = parser.parse_args(argv)
    work = None
    try:
        repo = args.repo.expanduser().resolve()
        if not (repo / 'lean-toolchain').is_file() or not (repo / 'Veir').is_dir():
            raise CatalogError(f'Not a VeIR checkout: {repo}')
        if not (repo / (PRINTER.replace('.', '/') + '.lean')).is_file():
            raise CatalogError(f'This checkout lacks {PRINTER}; use a checkout containing the Puddle pretty printer.')
        output = args.output.expanduser().resolve() if args.output else repo / 'docs/puddle-patterns.pdf'
        if output.suffix.lower() != '.pdf':
            raise CatalogError('--output must have a .pdf extension; the Markdown is saved beside it.')
        tools = {name: shutil.which(name) for name in ['lake', 'pandoc', 'typst']}
        missing = [name for name, path in tools.items() if not path]
        if missing:
            raise CatalogError('Required commands missing from PATH: ' + ', '.join(missing))
        body_font, code_font, fallback = fonts(tools['typst'], args.font, args.code_font)
        modules = discover_modules(repo)
        work_parent = args.work_dir.expanduser().resolve() if args.work_dir else repo / '.lake/puddle-catalog'
        work_parent.mkdir(parents=True, exist_ok=True)
        work = Path(tempfile.mkdtemp(prefix='run-', dir=work_parent))
        (work / 'modules.json').write_text(json.dumps(modules, indent=2) + '\n', encoding='utf-8')
        print(f'Discovered {len(modules)} candidate modules. Work directory: {work}', flush=True)
        if not args.skip_build:
            targets = sorted({PRINTER, EXECUTION, *modules})
            run([tools['lake'], 'build', *targets], repo, work / 'build.log', 'Building pattern modules')
        results = []
        for modern, label in [(False, 'legacy'), (True, 'modules')]:
            selected = [name for name in modules if modules[name] == modern]
            if not selected:
                continue
            path = work / (label + '.lean')
            exported = work / (label + '.jsonl')
            path.write_text(make_driver(selected, modern, exported), encoding='utf-8')
            run([tools['lake'], 'env', 'lean', '--tstack=400000', str(path)],
                repo, work / (label + '.log'), 'Exporting ' + label + ' patterns')
            results.append(exported)
        definitions, records = collect_records(results)
        validate_catalog(definitions, records)
        print(f'Validated {len(records):,} renderings covering {len(definitions):,} declarations.', flush=True)
        md_path = output.with_suffix('.md')
        text = markdown(repo, md_path, definitions, records)
        generated_md = work / 'puddle-patterns.md'
        generated_md.write_text(text, encoding='utf-8')
        pdf = render_pdf(text, repo, work, tools, body_font, code_font, fallback)
        publish(generated_md, md_path)
        publish(pdf, output)
        print(f'Saved {md_path}\nSaved {output}\nLogs and generated Lean: {work}')
        return 0
    except (CatalogError, OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f'error: {error}', file=sys.stderr)
        if work:
            print(f'Logs and intermediates retained at {work}', file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        print('\nInterrupted.', file=sys.stderr)
        return 130


if __name__ == '__main__':
    raise SystemExit(main())
