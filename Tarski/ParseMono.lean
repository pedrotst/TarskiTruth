import Tarski.Wff
import Tarski.GodelEncoding

open Lang
open Godel

/-!
# Phase 1 — fuel monotonicity and determinism for `parseFormula`

Mirrors the `parseAtom_succ … parseAdd_succ` mutual block of `Tarski/Wff.lean`
for the five formula-level parsers.
-/

theorem parseFormula_mono
    {fuel₁ fuel₂ : Nat} {xs : L_formula} {r : Formula × L_formula}
    (h₁₂ : fuel₁ ≤ fuel₂)
    (h : parseFormula fuel₁ xs = some r) :
    parseFormula fuel₂ xs = some r := by
  sorry

theorem parse_det
    {fuel₁ fuel₂ : Nat} {xs : L_formula} {φ₁ φ₂ : Formula}
    (h1 : parse fuel₁ xs = some φ₁)
    (h2 : parse fuel₂ xs = some φ₂) :
    φ₁ = φ₂ := by
  sorry

theorem decode_det
    {fuel₁ fuel₂ n : Nat} {φ₁ φ₂ : Formula}
    (h1 : decode fuel₁ n = some φ₁)
    (h2 : decode fuel₂ n = some φ₂) :
    φ₁ = φ₂ := by
  sorry
