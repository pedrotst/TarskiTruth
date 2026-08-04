# Plan: closing all open proofs in TarskiTruth

Goal: `tarski : ¬ IsArithmeticSet T` in `Tarski/Arithmetic.lean` with **zero
`sorry`s** anywhere in the library, verified by a clean `lake build`.

The main theorem's proof script is already complete — it only depends on named
holes. This plan closes those holes. It is **not** a straight-line "fill in the
sorries" plan, because the audit found that (a) three helper lemmas are false as
stated, (b) two proof blocks currently fail to compile, (c) `lake build` does
not actually check the two files containing the sorries, and (d) the central
hole `diagonalR_arith` is infeasible under the current definition of
`diagonalR` and requires a definition change (see Phase 4).

---

## Audit summary (ground truth as of 2026-08-03)

### Open sorries

| # | Location | Lemma | Status |
|---|----------|-------|--------|
| 1 | `Arithmetic.lean:237,238` | `diagonalR_arith` | broken proof + **infeasible as defined** → Phase 4 |
| 2 | `Arithmetic.lean:311` | `star_arithmetic` | broken proof, wrong witness → Phase 5 |
| 3 | `Arithmetic.lean:323` | `diagonalR_encode` | → Phase 4 |
| 4 | `Arithmetic.lean:329` | `diagonalR_functional` | → Phase 4 |
| 5 | `Arithmetic.lean:334` | `T_encode_closed` | → Phase 6 |
| 6 | `Wff.lean:647` | `parseTerm_append_rpar` | true; subsumed by Phase 2 |
| 7 | `Wff.lean:653` | `parseTerm_append_plus` | **FALSE — delete** |
| 8 | `Wff.lean:660` | `parseTerm_plus_closed` | **FALSE — delete** |
| 9 | `Wff.lean:703–705` | `wff_parseTerm` (3 cases) | obsolete — delete (see Phase 2) |
| 10 | `Wff.lean:709` | `wff_parse` | obsolete — delete (see Phase 2) |
| 11 | `Wff.lean:713` | `parse_sound` | **FALSE — delete** |
| 12 | `Wff.lean:779` | `append_S_ne_var_replicate_prime` | obsolete — delete with injectivity chain |
| 13 | `Wff.lean:816–817` | `unparse_injective` | re-derive as corollary in Phase 2 |

### Compile errors (must fix before anything else)

- `Arithmetic.lean:232` — `exists (diagSentence)`: type error
  (`diagSentence : Formula → Formula`, goal wants `Formula`). Lines 234, 304,
  306 have failing tactics downstream of it.
- `Wff.lean:781` (`unparse_term_injective`) — missing induction cases / stray
  code; 9 errors.

### False lemmas (verified by `#eval` counterexamples)

- `parse_sound : parse fuel l = some φ → unparse φ = l`
  Counterexample: `parse 10 [⋎,+,⋎,=,O] = some (eq (add v v) zero)`, but
  `unparse` of that is `[(,⋎,+,⋎,),=,O]` — the parser accepts non-canonical
  (unparenthesized) strings; `unparse` re-parenthesizes.
- `parseTerm_append_plus : parseTerm fuel l = some (t,[]) →
  parseTerm fuel (l ++ [+] ++ r) = some (t, +::r)`
  Counterexample: `parseTerm 10 [⋎,+,⋎] = some (add v v, [])` — `parseAddLoop`
  consumes the `+`; it never stops in front of one.
- `parseTerm_plus_closed : … parseTerm fuel (l₁ ++ [+] ++ l₂) = some (add t₁ t₂, [])`
  Counterexample: `l₁ = [⋎]`, `l₂ = [⋎,+,⋎]`. Parsing is left-associative:
  `parseTerm 10 [⋎,+,⋎,+,⋎] = add (add v v) v`, but `add t₁ t₂ = add v (add v v)`.

Consequence: the intended proof route for the round-trip theorem
(`unparse_wff → wff_parse → parse_sound → unparse_injective`, assembled in
`unparse_parse_closed`) is dead. Phase 2 replaces it with a direct induction,
which also makes `wff_parseTerm`, `wff_parse`, and the broken syntactic
injectivity development (`unparse_term_injective`,
`append_S_ne_var_replicate_prime`, `unparse_injective`) unnecessary —
injectivity falls out as a corollary.

### Build system gap

`lakefile.lean` declares `lean_lib Tarski` but there is no root module
`Tarski.lean`, so `lake build` compiles **nothing** (only `Lang`,
`GodelEncoding`, `Environment` have oleans, built on demand). `Wff.lean` and
`Arithmetic.lean` — the files with all the sorries and errors — are never
checked by the build. Also, nothing imports `Tarski.Wff`, so parser results are
not yet visible from `Arithmetic.lean`.

---

## The strategic decision: redefine `diagonalR`

**Problem.** `diagonalR n m` (`GodelEncoding.lean:127`) currently means
"`decode fuel n` succeeds with `φₙ`, and `m = ⌜diagAt n φₙ⌝`". A formula
expressing this must arithmetize "n codes a parseable string" — i.e. a full
Gödel-style arithmetization of the parser (sequence coding / β-function), a
months-scale project with no Mathlib to lean on. Worse, when `n` is a
*non-canonical* code, `m` depends on the code of the **re-canonicalized**
formula, so the relation is not a simple function of `n` at all.

**Observation.** The `tarski` proof uses `diagonalR` through exactly three
facts:

1. `diagonalR_arith` — the relation is arithmetic;
2. `diagonalR_functional` — it is a partial function;
3. `diagonalR_encode` — it sends `⌜ψ⌝` to `⌜diagSentence ψ⌝` for every `ψ`.

Any relation with these three properties makes the proof go through; `T` and
the statement of `tarski` are untouched, so the theorem proven is the same.

**Solution.** On canonical codes, diagonalization is a *polynomial in `n`,
`17ⁿ`, and `17ᵏ`* (k = base-17 digit-length of n), because `symbolCode S = 0`
and `encodeL` is a base-17 fold:

```
unparse (diagAt n φ)
  = [∀,⋎,(,(,⋎,=,O] ++ replicate n S ++ [→] ++ unparse φ ++ [),)]

codes:  ∀=15 ⋎=7 (=9 ==5 O=1 S=0 →=14 )=10
C := encodeL [∀,⋎,(,(,⋎,=,O] = 372800549
```

For canonical `n = ⌜φ⌝` with digit-length `k` (`encodeL (unparse φ) = n`,
`(unparse φ).length = k`):

```
⌜diagAt n φ⌝ = ((((C * 17^n) * 17 + 14) * 17^k + n) * 17 + 10) * 17 + 10
```

So **redefine** (Phase 4):

```lean
def diagF (n k : Nat) : Nat :=
  ((((372800549 * 17 ^ n) * 17 + 14) * 17 ^ k + n) * 17 + 10) * 17 + 10

def diagonalR (n m : Nat) : Prop :=
  ∃ k, n < 17 ^ k ∧ 17 ^ k ≤ 17 * n ∧ m = diagF n k
```

The two constraints say `17^(k-1) ≤ n < 17^k` (for `n ≥ 1`), i.e. `k` is the
base-17 digit-length of `n` — unique, hence functionality is easy. `n = 0`
relates to nothing (fine: 0 is not a code — every `unparse` head symbol has
nonzero code). The language has `exp`, so the defining formula is directly
writable with `.exp`, and the huge numeral `term_of_nat 372800549` is only ever
manipulated symbolically (via `term_of_nat_sound`), never evaluated.

The rejected alternative — keeping the decode-based definition and
arithmetizing the parser — is recorded here so we don't relitigate it: it is
5–10× the work and strictly harder mathematics, for the same end theorem.

---

## Phases

Dependency graph: Phase 0 first; Phases 1, 2, 3 are then independent of each
other; Phase 4 needs 3; Phase 5 needs 4 (statement only); Phase 6 needs 1+2+3.
`tarski` closes when 4, 5, 6 land.

```
0 ─┬─ 1 (parseFormula fuel-mono) ──┬─ 6 (T_encode_closed) ─┐
   ├─ 2 (round-trip)  ─────────────┤                        ├─ tarski ✓
   ├─ 3 (encoding round-trip) ──┬──┘                        │
   │                            └─ 4 (new diagonalR) ── 5 ──┘
```

---

### Phase 0 — Make the repo honest (~1 hour)

Everything compiles after this phase; only `sorry` warnings remain.

- [ ] Create root `Tarski.lean`:
      `import Tarski.Lang / Wff / GodelEncoding / Environment / Arithmetic`
      (leave `Playground` out or include it — decide by whether it compiles).
      Verify `lake build` now reports jobs and fails on the current errors.
- [ ] Add `import Tarski.Wff` to `Arithmetic.lean` (needed by Phase 6; do it
      now so the namespace is settled).
- [ ] `Wff.lean`: delete the false lemmas `parse_sound`,
      `parseTerm_append_plus`, `parseTerm_plus_closed`; delete `wff_parseTerm`,
      `wff_parse`, `unparse_term_injective`, `append_S_ne_var_replicate_prime`,
      `unparse_injective`, and the current `unparse_parse_closed` /
      `unparse_parse_id` bodies (restate the last two with `sorry` — they are
      re-proven in Phase 2). Keep `parseTerm_append_rpar` as a `sorry`d
      statement (Phase 2 proves a generalization).
- [ ] `Arithmetic.lean`: stub `diagonalR_arith` and `star_arithmetic` as
      `sorry` at the top of their proofs (removing the broken `exists
      (diagSentence)` witness and failing tactic lines).
- [ ] `lake build` → success, sorry-warnings only. Commit: "Phase 0: honest
      baseline".

### Phase 1 — `parseFormula` fuel-monotonicity (~250 lines, mechanical)

Mirror the existing `mutual` block `parseAtom_succ … parseAdd_succ`
(`Wff.lean:244–519`) for the five formula-parser functions.

- [ ] `mutual` block with, for each of `parseFormula.parseAtomic`,
      `parseQuantifier`, `parseNot`, `parseBase`, `parseImp`:
      `parseX_succ : parseX fuel xs = some r → parseX (fuel+1) xs = some r`
      (same `termination_by (fuel, i)` / `Prod.Lex` pattern; `parseAtomic`
      needs `parseTerm_succ`, already proven).
- [ ] `parseFormula_succ`, then
      `parseFormula_mono : fuel₁ ≤ fuel₂ → parseFormula fuel₁ xs = some r →
      parseFormula fuel₂ xs = some r` (copy `parseTerm_mono`).
- [ ] `parse_mono` and `parse_det :
      parse fuel₁ xs = some φ₁ → parse fuel₂ xs = some φ₂ → φ₁ = φ₂`.
- [ ] Corollary `decode_det :
      decode fuel₁ n = some φ₁ → decode fuel₂ n = some φ₂ → φ₁ = φ₂`
      (decode is `decodeL` — fuel-free — then `parse`).

### Phase 2 — Round-trip theorem, direct route (~300–400 lines; largest Wff item)

Replace the dead `wff_parse`/`parse_sound` route. Key idea: every
`unparse_term` output has shape `atom ++ replicate k S` where compound atoms
are parenthesized, and every `unparse` formula output is fully
parenthesized/prefixed — so parsing canonical strings is syntax-directed.

Define the safe-suffix predicate: the empty list, or any list whose head is
**not** a token the term parsers can consume past a completed term:

```lean
def termSafe : L_formula → Prop
  | [] => True
  | a :: _ => a ∉ [L.S, L.prime, L.plus, L.mult, L.exp]
```

(`S` feeds `parseSuccLoop`, `'` feeds `countPrimes`, `+`/`x`/`E` feed the
add/mul/exp loops. The heads that actually occur after a term in formula
contexts — `=`, `≤`, `)`, `∧`, `∨`, `→` — are all safe.)

- [ ] `countPrimes_append :
      head rest ≠ L.prime →
      countPrimes (List.replicate m L.prime ++ rest) = (m, rest)`
      (generalizes existing `countPrimes_replicate`).
- [ ] Term-level round-trip, by induction on `t` with levels handled
      separately (use the existing `_succ`/`parseTerm_mono` family to combine
      fuels from IHs):
      `parse_unparse_term : ∀ t rest, termSafe rest →
      ∃ fuel, parseTerm fuel (unparse_term t ++ rest) = some (t, rest)`.
      Case notes:
      - `var n`: `parseVar` + `countPrimes_append` (needs head rest ≠ `'`).
      - `zero`: immediate.
      - `succ t`: the tricky one — strengthen to track the `Sᵏ` tail through
        `parseSuccLoop` (helpers `parseSuccLoop_replicate_S` and
        `replicate_S_append_one` at `Wff.lean:565,580` already exist; needs an
        append-aware variant `parseSuccLoop fuel t (replicate k S ++ rest) =
        some (succ^k t, rest)` for rest with head ≠ S).
      - `add/mul/exp`: parenthesized atoms; inner parse at top level with
        `rest' = [op] ++ … ++ [)] ++ rest`, glue with the loop equations.
- [ ] `parseTerm_append_rpar` (the existing sorry) becomes the instance
      `rest = [L.r_par]` — restate as corollary or prove the general
      `parseTerm_extend : parseTerm fuel l = some (t, []) → termSafe rest →
      ∃ fuel', parseTerm fuel' (l ++ rest) = some (t, rest)`? **No** — that
      general form is false for non-canonical `l` continuations; keep only the
      `unparse_term`-shaped statement above and derive the `r_par` case used
      by nothing after this phase (delete if unused).
- [ ] Formula-level round-trip, induction on `φ`:
      `parse_unparse_formula : ∀ φ rest, formSafe rest →
      ∃ fuel, parseFormula fuel (unparse φ ++ rest) = some (φ, rest)`
      where `formSafe rest`: `rest = []` or head ∈ `{), ∧, ∨, →}`.
      Each case is prefix-directed (`¬(…)`, `(…op…)`, `∀⋎'…(…)`); the `eq`/`le`
      cases feed `termSafe` suffixes to the term lemma. Note
      `parseNot`/`parseBase` overlap: for non-`¬` heads `parseNot` falls
      through to `parseBase` — follow the actual defeq path, and reuse
      `parseQuantifier0_none`-style dispatch lemmas where the head decides the
      branch.
- [ ] `unparse_parse_id : ∀ φ, ∃ fuel, parse fuel (unparse φ) = some φ`
      (instantiate `rest := []`).
- [ ] `unparse_injective : unparse ψ = unparse φ → ψ = φ` — corollary:
      round-trip both sides, rewrite, apply `parse_det` (Phase 1). This
      replaces the deleted broken development.

### Phase 3 — Base-17 encoding round-trip (~150 lines, `GodelEncoding.lean`)

- [ ] `codeSymbol_symbolCode : ∀ s, codeSymbol (symbolCode s) = some s`
      (17 cases; `decide` or `cases s <;> rfl`).
- [ ] `symbolCode_lt : ∀ s, symbolCode s < 17`.
- [ ] `encodeL_append :
      encodeL (l₁ ++ l₂) = encodeL l₁ * 17 ^ l₂.length + encodeL l₂`
      (induction on `l₂` from the right, or prove the foldl step lemma
      `encodeL_snoc` first).
- [ ] Upper bound `encodeL_lt : encodeL l < 17 ^ l.length`.
- [ ] Lower bound `le_encodeL : symbolCode a ≠ 0 →
      17 ^ l.length ≤ encodeL (a :: l)`.
- [ ] `unparse_head_code_ne_zero : ∀ φ, ∃ a l, unparse φ = a :: l ∧
      symbolCode a ≠ 0` — heads are `⋎,O,(,¬,∀,∃` (codes 7,1,9,11,15,16);
      cases on `φ` (and on the leading term for `eq`/`le`).
- [ ] Digits round-trip: `digits17_encodeL :
      symbolCode a ≠ 0 → (∀ s ∈ l, True) →   -- codes < 17 automatic
      digits17L (encodeL (a :: l)) = (a :: l).map symbolCode`.
      Proof by induction from the right using `digits17Helper`'s div/mod
      unfolding and `encodeL_snoc`; the head condition keeps the leading digit
      alive. Then `decodeDigitsL_map : decodeDigitsL (l.map symbolCode) =
      some l` via `codeSymbol_symbolCode`.
- [ ] Assemble `decodeL_encode : decodeL ⌜φ⌝ = some (unparse φ)` and, with
      Phase 2, `decode_encode : ∃ fuel, decode fuel ⌜φ⌝ = some φ`.

### Phase 4 — New `diagonalR` + its three lemmas (~250 lines)

- [ ] In `GodelEncoding.lean`: replace `diagonal` / `diagonalR` with `diagF` /
      `diagonalR` as specified in the strategy section. Keep `diagAt`,
      `diagSentence` unchanged. Delete `diagonal_formula` / `diagonal` (or
      leave them `#eval`-only; nothing may depend on them).
- [ ] Pow order toolkit (no Mathlib — check core `Nat` lemmas first, hand-roll
      the rest): `Nat.pow_lt_pow_right`-style strict mono in exponent for base
      ≥ 2, `pow_le_pow_iff`, and "digit-length is unique":
      `k_unique : n < 17^k → 17^k ≤ 17*n → n < 17^k' → 17^k' ≤ 17*n → k = k'`.
- [ ] `diagonalR_functional : diagonalR n m₁ → diagonalR n m₂ → m₁ = m₂`
      — from `k_unique`, then `diagF` is a function.
- [ ] `diagonalR_encode : ∀ ψ, diagonalR ⌜ψ⌝ ⌜diagSentence ψ⌝`:
      witness `k := (unparse ψ).length`; constraints from `encodeL_lt` /
      `le_encodeL` / `unparse_head_code_ne_zero` (Phase 3); the equation
      `⌜diagSentence ψ⌝ = diagF ⌜ψ⌝ k` by expanding
      `unparse (diagAt ⌜ψ⌝ ψ)` and chaining `encodeL_append` (note
      `encodeL (replicate n S) = 0` ⇒ the `Sⁿ` block is exactly `* 17^n`;
      needs `unparse_term (term_of_nat n) = L.O :: replicate n L.S`, an easy
      induction).
- [ ] `diagFormula : Formula` — the object-language formula:
      `.exists_ 2 (…)` encoding
      `∃k, v₀ < 17^k ∧ 17^k ≤ 17·v₀ ∧ v₁ = ((((C·17^v₀)·17+14)·17^k+v₀)·17+10)·17+10`
      using vars 0 (=n), 1 (=m), 2 (=k); `<` as `≤ ∧ ¬ =` or via `succ`;
      numerals via `term_of_nat`.
- [ ] `diagonalR_arith : IsArithmeticRel2 diagonalR` with witness
      `diagFormula`: the `only_free_var_zero_one` side is `fv` computation
      (`simp [fv, fv_term]`); the semantic side is `term_of_nat_sound` +
      `simp` + the pow toolkit. Nothing here evaluates `17^n` or the numeral
      `C` concretely.

### Phase 5 — Coincidence, renaming, `star_arithmetic` (~250 lines, `Arithmetic.lean`)

- [ ] **Coincidence lemma** (new, load-bearing):
      `eval_coincide : (∀ x ∈ fv φ, σ x = σ' x) →
      (evalFormula σ φ ↔ evalFormula σ' φ)`
      plus the term version for `evalTerm`. Structural induction; quantifier
      cases extend the agreement through `update` (helper: `x ∈ fv (forall_ n p)
      ↔ x ∈ fv p ∧ x ≠ n`).
- [ ] Usable characterizations (upgrade the fixed-assignment interfaces):
      - `expressesSet_eval : ExpressesSet φ S → ∀ ρ, (evalFormula ρ φ ↔ S (ρ 0))`
        via `evalFormula_subst_update` (proven) + `eval_coincide`.
      - `expressesRel2_eval : ExpressesRel2 ψ R → ∀ ρ,
        (evalFormula ρ ψ ↔ R (ρ 0) (ρ 1))` via `eval_coincide` directly.
- [ ] **Variable swap** (bijective rename — no capture side-conditions, unlike
      `subst (.var 1)` which can capture under a `forall_ 1` binder):
      `swapNat : Nat → Nat` (0↔1, id elsewhere), `swapTerm`, `swap01 :
      Formula → Formula` renaming **all** occurrences including binders.
      - `eval_swap : evalFormula σ (swap01 φ) ↔ evalFormula (σ ∘ swapNat) φ`
        (induction; binder case: `update (σ ∘ swapNat) (swapNat x) n =
        (update σ x n) ∘ swapNat` — an `Env` lemma next to `env_comm`).
      - `fv_swap : x ∈ fv (swap01 φ) ↔ swapNat x ∈ fv φ`.
- [ ] `star_arithmetic : IsArithmeticSet S → IsArithmeticSet (star S)` —
      **rewrite from scratch** (current script reuses `ψ` alone as witness,
      which cannot work). Witness: `χ := .exists_ 1 (.and ψ (swap01 φ))`
      where `ψ` from `diagonalR_arith`, `φ` from `S`.
      - `only_free_var_zero χ`: from `fv` of `.exists_`/`.and`, `h1`
        (fv ψ ⊆ {0,1}), `fv_swap` (fv (swap01 φ) ⊆ {1}).
      - Semantics: fix `n`; `evalFormula (update empty_ctx 0 n) χ`
        unfolds to `∃ m, eval (update (update … 0 n) 1 m) ψ ∧ eval … (swap01 φ)`;
        apply `expressesRel2_eval` (gives `diagonalR n m`) and `eval_swap` +
        `expressesSet_eval` (gives `S m`); conclude `↔ star S n`. Convert to
        the `subst (term_of_nat n)` form via `evalFormula_subst_update`.

### Phase 6 — `T_encode_closed` and final assembly (~50 lines)

- [ ] `T_encode_closed : closed φ → (T ⌜φ⌝ ↔ evalFormula empty_ctx φ)`:
      - (→) unpack `⟨fuel, φ', hdec, hclosed, heval⟩`; `decode_encode`
        (Phase 3) gives `decode fuel₀ ⌜φ⌝ = some φ`; `decode_det` (Phase 1)
        gives `φ' = φ`; rewrite.
      - (←) witness the fuel from `decode_encode`; `closed φ` and the
        hypothesis close the conjunction.
- [ ] Confirm `tarski` compiles with no remaining holes (its script is
      untouched throughout).
- [ ] Sweep: `grep -rn "sorry" Tarski/` → empty; `lake build` from clean
      (`lake clean` first) → success, no sorry warnings.
- [ ] Optional hygiene: decide fate of `Playground.lean`; add the
      root-module build check to CI if any exists.

---

## Effort and sequencing notes

- Phases 1 and 3 are mechanical (existing patterns to copy); Phase 2 is the
  largest Wff effort — the `succ`/`parseSuccLoop` interaction and fuel
  bookkeeping need care, but `parseTerm_mono` + the `_succ` family already
  absorb the fuel pain.
- Phases 4–5 are the mathematically new work; total new code ≈ 1.2–1.5k lines.
- Each phase ends with a green `lake build` and a commit; phases 1/2/3 can be
  interleaved freely after Phase 0.
- Optional epilogue (not required for `tarski`): relate new `diagonalR` to the
  old decode-based intent on canonical codes:
  `diagonalR ⌜ψ⌝ m ↔ m = ⌜diagSentence ψ⌝` — one line from `_functional` +
  `_encode`.
