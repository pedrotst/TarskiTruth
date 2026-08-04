# PROGRESS — closing all proofs in TarskiTruth

Companion to `PLAN.md`. Read this first in a fresh session: it records what is
done, what the current file layout is, and the gotchas that cost time.

## Current status

| Phase | What | State |
|---|---|---|
| 0 | honest baseline, root module, file split | **done** |
| 1 | `parseFormula` fuel-mono, `parse_det`, `decode_det` | **done** |
| 2 | round-trip `parse (unparse φ) = φ` | in progress |
| 3 | base-17 encoding round-trip | **done** |
| 4 | `diagonalR_functional`, `diagonalR_arith`, `diagonalR_encode` | **done** |
| 5 | `eval_coincide`, `swap01`, `star_arithmetic` | **done** |
| 6 | `T_encode_closed`, `tarski` | **done** |

**One sorry left in the whole library:** `unparse_parse_id` in
`Tarski/RoundTrip.lean`. Everything else is closed.

`#print axioms` confirms `star_arithmetic`, `diagonalR_arith`,
`diagonalR_encode`, `diagonalR_functional`, `decodeL_encode` are all free of
`sorryAx`; `tarski` reaches `sorryAx` only through
`T_encode_closed → decode_encode / decode_det → unparse_parse_id / ParseMono`.

## File layout (post Phase 0)

| File | Contents | Depends on |
|---|---|---|
| `Tarski/Lang.lean` | syntax, `unparse`, `parseTerm`, `parseFormula` | — |
| `Tarski/Wff.lean` | wff predicates, `parseTerm` fuel-monotonicity family | Lang |
| `Tarski/ParseMono.lean` | Phase 1: `parseFormula` fuel-mono, `parse_det`, `decode_det` | Wff, GodelEncoding |
| `Tarski/RoundTrip.lean` | Phase 2: `parse (unparse φ) = φ` | ParseMono |
| `Tarski/GodelEncoding.lean` | base-17 codes, `encode`, `decode`, `diagF`, `diagonalR` | Lang |
| `Tarski/EncodingLemmas.lean` | Phase 3: `encodeL_append`, bounds, `decodeL_encode` | GodelEncoding |
| `Tarski/Environment.lean` | assignments | — |
| `Tarski/Semantics.lean` | Phase 5a: `eval_coincide`, `swap01` toolkit | Lang, Environment, Arithmetic-core |
| `Tarski/Diagonal.lean` | Phase 4: `diagFormula`, the three `diagonalR` lemmas | EncodingLemmas, Semantics |
| `Tarski/Arithmetic.lean` | model, `IsArithmeticSet`, `star_arithmetic`, `tarski` | everything |
| `Tarski.lean` | root module so `lake build` actually checks the library | all |

## THE GRAMMAR CHANGE (2026-08-04) — read this before touching the parser

PLAN.md's audit missed that **`unparse_parse_id` was false as originally stated**.
`parseFormula.parseBase` dispatched a `(` head straight into the
parenthesised-*formula* branch with a `do`-bind and no backtracking.  When the `(`
was actually a *term's* paren — i.e. an atomic formula whose left-hand term is an
`add`/`mul`/`exp` — the inner `parseImp` failed and `parseBase` returned `none`
without ever trying `parseAtomic`.  Enumeration over 13194 formulas: 12312 failed
(zero mis-parses; failures were always `none`).  Minimal counterexample:

    parse n (unparse (Formula.eq (.add .zero .zero) .zero)) = none   for every n

`star_arithmetic`'s witness contains `.le (.exp …) (.mul …)`, so the main theorem
genuinely needed this fixed, not worked around.

**Fix chosen: atomic formulas are now prefix-marked.**

    unparse (.eq m n) = L.eq  :: (unparse_term m ++ unparse_term n)
    unparse (.le m n) = L.leq :: (unparse_term m ++ unparse_term n)

and `parseFormula.parseBase` now dispatches purely on the head symbol
(`(` → parenthesised formula, `∀`/`∃` → quantifier, `=`/`≤` → atomic, else
`none`).  Terms are self-delimiting, so `= t₁ t₂` needs no separator.

Why this rather than making `parseBase` backtrack: with backtracking,
`parseBase_succ` (fuel monotonicity) needs "`parseAtomic` and the paren-formula
branch never both succeed", which is a genuine disjointness theorem about the two
languages. Head-dispatch removes the ambiguity at the source, so monotonicity is
mechanical again. Verified empirically: 1360/1360 sampled formulas round-trip.

Consequences already applied: `diagC` is now **372800005** (was 372800549), the
`wff_eq`/`wff_leq` constructors carry the prefix shape, and
`unparse_head_code_ne_zero` got easier (heads are literally `=`/`≤`).
`unparse_term` and `parseTerm` are **unchanged**.

## Gotchas (hard-won)

1. **`lake build` used to compile nothing.** `lakefile.lean` declares
   `lean_lib Tarski` but there was no root `Tarski.lean`. Always verify
   `lake build` reports a nonzero job count.
2. **Never let any tactic evaluate `term_of_nat 372800549`.** It is a unary
   numeral of ~3.7e8 constructors. Use `term_of_nat_sound` (for `evalTerm`) and
   `closed_term_of_nat` (for `fv_term`). Never `decide`, never `simp [term_of_nat]`,
   never `native_decide` on anything containing it.
3. **Three lemmas in the old `Wff.lean` were FALSE** (`parse_sound`,
   `parseTerm_append_plus`, `parseTerm_plus_closed`) — see PLAN.md's audit for the
   `#eval` counterexamples. Deleted in Phase 0; do not resurrect.
4. The parser accepts non-canonical strings (`[⋎,+,⋎,=,O]` parses), so
   `parse ∘ unparse = id` holds but `unparse ∘ parse = id` does NOT.
5. `digits17Helper` had an off-by-one (emitted the *predecessor* mod 17). Fixed.
6. `unparse`, `substTerm`, `subst`, `evalTerm`, `evalFormula`, `symbolCode`,
   `encodeL`, `decodeL` are all `@[simp]`. A bare `simp` unfolds a lot. `fv`,
   `fv_term`, `term_of_nat` are not.

## Log

- 2026-08-03: session start. Baseline audit matches PLAN.md.
- 2026-08-03: Phase 0 done; Phases 5+6 done (Arithmetic.lean sorry-free).
- 2026-08-04: Phases 1, 3 done; Phase 4 done except `diagonalR_encode`.
- 2026-08-04: grammar change (see above); Phase 1 being redone against it.
- 2026-08-04: Phase 1 redone against the new dispatch (no disjointness lemmas
  needed — roughly half the size of the pre-fix version).
- 2026-08-04: Phase 4 fully closed (`diagonalR_encode` via `unparse_diagAt` +
  `encodeL_snoc`/`encodeL_append` peeling; `encodeL diagPrefix = diagC` by `decide`).
