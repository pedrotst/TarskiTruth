# PROGRESS — closing all proofs in TarskiTruth

Companion to `PLAN.md`. Read this first in a fresh session: it records what is
done, what the current file layout is, and the gotchas that cost time.

## Current status

- **Phase 0 (honest baseline): in progress**

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
5. `unparse`, `substTerm`, `subst`, `evalTerm`, `evalFormula`, `symbolCode`,
   `encodeL`, `decodeL` are all `@[simp]`. A bare `simp` unfolds a lot. `fv`,
   `fv_term`, `term_of_nat` are not.

## Log

- 2026-08-03: session start. Baseline audit matches PLAN.md.
