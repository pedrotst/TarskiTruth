import Tarski.GodelEncoding
import Tarski.RoundTrip

open Lang
open Godel

/-!
# Phase 3 — the base-17 encoding round-trip
-/

theorem encodeL_append (l₁ l₂ : L_formula) :
    encodeL (l₁ ++ l₂) = encodeL l₁ * 17 ^ l₂.length + encodeL l₂ := by
  sorry

theorem encodeL_lt (l : L_formula) : encodeL l < 17 ^ l.length := by
  sorry

theorem le_encodeL {a : L} (l : L_formula) (h : symbolCode a ≠ 0) :
    17 ^ l.length ≤ encodeL (a :: l) := by
  sorry

theorem unparse_head_code_ne_zero (φ : Formula) :
    ∃ a l, unparse φ = a :: l ∧ symbolCode a ≠ 0 := by
  sorry

theorem decodeL_encode (φ : Formula) : decodeL (encode φ) = some (unparse φ) := by
  sorry

theorem decode_encode (φ : Formula) : ∃ fuel, decode fuel (encode φ) = some φ := by
  sorry
