import Tarski.ParseMono

open Lang

/-!
# Phase 2 — the round-trip theorem `parse (unparse φ) = some φ`
-/

theorem unparse_parse_id : ∀ φ : Formula,
    ∃ fuel, parse fuel (unparse φ) = some φ := by
  sorry
