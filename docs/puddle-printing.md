# Reading Puddle rewrites

The [generated catalog](puddle-patterns.md) contains output for all production
Puddle pattern declarations, with parameter choices and source links.

Regenerate the Markdown and [PDF](puddle-patterns.pdf) from a checkout with:

```sh
python3 Tools/puddle_catalog.py /path/to/veir
```

The script rebuilds the Lean modules, discovers production pattern declarations,
runs the Lean pretty printer, and renders the result. It writes
`docs/puddle-patterns.md` and `docs/puddle-patterns.pdf` in that checkout. It is
self-contained and can also be copied outside the repository; the target checkout
must contain `Veir.PatternRewriter.Puddle.PrettyPrinter`.

Requirements: Python 3.9 or later, `lake` with the checkout's Lean toolchain,
`pandoc`, and `typst` on `PATH`. No Python packages are needed. Rendering was
tested with Pandoc 3.12.1 and Typst 0.15.1. Install a monospace font such as
DejaVu Sans Mono; the script selects installed fonts automatically, or accepts
`--font` and `--code-font`. If Poppler's `pdftotext` is installed, it also checks
that all code blocks survived PDF rendering and fit within the page margins.

To choose another destination, or reuse current Lean build products:

```sh
python3 Tools/puddle_catalog.py . --output /tmp/puddle-patterns.pdf
python3 Tools/puddle_catalog.py . --skip-build
```

Relative output paths are relative to the calling directory. Markdown is always
saved beside the PDF with the same base name. Logs, generated Lean exporters,
and intermediate files remain in `.lake/puddle-catalog/run-*` in the checkout;
`--work-dir` changes their parent directory. Generation and validation must
succeed before the script replaces the published files.

The catalog includes every discovered named production `Pattern OpCode`
definition, including aliases and direct records, plus concrete compiled pass
instances. Counts and source links are derived from the checkout. Scalar
parameters remain symbolic; graph-dependent choices use explicit cases. The
catalog's parameter-coverage section describes finite choices and representative
GEP arities, which do not enumerate the unbounded families. New scalar-parametric
patterns are handled automatically. Unsupported graph-dependent patterns fail
with a diagnostic; extend `catalogExpand` or `pass_instances()` in the script
when adding new kinds of graph parameters. Coverage checks reject omitted
declarations and failed renderings.

Import the printer and the module defining a pattern, then use `#print_puddle`:

```lean
import Veir.PatternRewriter.Puddle.PrettyPrinter
import Veir.InstSimplify.IS0609
import Veir.InstSimplify.IS5150
import Veir.InstSimplify.IS3341

#print_puddle Veir.InstSimplify.IS0609.pattern
#print_puddle Veir.InstSimplify.IS5150
#print_puddle Veir.InstSimplify.IS3341_mulUdiv 2 8
```

Run the file with `lake env lean path/to/file.lean`, or read the messages in the
Lean editor. The command is also available through `Veir.PatternRewriter.Puddle`.

The examples start with these summaries:

```text
llvm: (X + 0)  =>  X
llvm: select(X, 1, 0)  =>  X
llvm: icmp(udiv((X * 2), 8), X)  =>  0
```

Each summary is separated from its `where` block by a blank line and uses a larger
font in the PDF. **The conditions in that block are
part of the rewrite.** For example, the select rule requires an integer type of
width 1, and the comparison rule requires the `ugt` predicate and a bound on the
constants. The summary alone does not express those requirements.

The notation follows the expression-oriented comments in LLVM's InstSimplify
and InstCombine. It is intended for reading, not parsing back into a pattern:

- `X`, `Y`, `Z`, and `X3`, ... are free SSA values. Repeated names denote the same
  value. Parentheses make grouping explicit. Generated value, operation, type,
  and property names gain suffixes such as `_1` when needed to avoid collisions
  with symbolic parameters. Global Lean constants are qualified when their
  names would collide with graph references.
- `T0`, `T1`, ... are type handles; `P0`, `P1`, ... are operation properties.
  Type equality, property predicates, and overflow flags remain visible in the
  `where` block. Unconstrained matched properties are not assumed to be defaults.
- `root` names the operation being replaced. `a0`, ... name other matched
  operations. Shared subexpressions use these names instead of duplicating the
  expression. Operations with identical printed expressions also use names in
  the summary, preserving their identity and operand order. The `where` block
  always uses named operand references to describe the exact graph.
- `C0`, ... name constants. Simple integer payload predicates and APInt bit
  predicates can be displayed as literals; recognition uses definitional
  equality, not predicate sampling. Their original guards remain in the output.
  Bit predicates use literal notation only when the compared type handle is the
  constant's result type handle. Compound symbolic payloads are parenthesized.
  More complicated constant predicates stay as named constants with explicit
  conditions.
- LLVM's `mlir.zero` and `mlir.poison` operations display as `0` and `poison`,
  respectively, in both summaries and `where` blocks, including across dialects.
- `new0`, ... and `[created]` mark new operations. All created operations are
  listed in creation order, including those whose results are not replacements.
  Reusing a matched value is different from creating a new operation.
- `.0`, `.1`, ... select results of a multi-result operation. A tuple on the
  right of `=>` lists replacements in root-result order. `=> ()` erases a root
  with no results; the `where` block still lists any creations.
- `require` introduces a guard. `outputs ← expression` is an optional metadata
  computation: it must return `some outputs`. `inspect root using ...` retains
  a contextual inspection. Guards and inspections appear in matcher execution
  order, followed by creation metadata computations in creation order.
- A leading dialect name qualifies the operators in a single-dialect rewrite.
  Rewrites crossing dialects use fully qualified operation names instead. Their
  `where` blocks also qualify recognized constants, for example
  `C1 = gmir.g_constant(0) : T0 [created]`, even when the summary uses a literal.

The printer reduces the existing Puddle builders into `MatchDecl`, `CreateDecl`,
and `Replacement` data. It works with helpers and pattern families without
reading their source files or requiring display annotations. It retains native
functions as Lean expressions; it does not attempt to infer arbitrary predicates
or reconstruct source comments.

Parameters that determine the graph must be supplied, such as a Boolean choosing
operand order. Parameters used only in predicates can remain symbolic:

```lean
section
variable (n : Int)
#print_puddle Veir.InstSimplify.IS3341_mulUdiv n 8
end
```

Use the uncompiled `Pattern`, before `Pattern.compile` erases it into a rewrite
closure. The metaprogramming API is
`Veir.Puddle.PrettyPrinter.format : Lean.Expr → Lean.MetaM Lean.Format`; it expects
an elaborated expression of type `Pattern OpCode`. The command runs at elaboration
time so it can retain and print the bodies of native predicates, which are opaque
functions at runtime.
