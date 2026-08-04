import Tarski.GodelEncoding
import Tarski.RoundTrip

open Lang
open Godel

/-!
# Phase 3 — the base-17 encoding round-trip
-/

/-! ## Generic helpers -/

/-- Reverse (snoc) induction on lists; Lean core has no `List.reverseRecOn`. -/
theorem list_rev_rec {α : Type} {motive : List α → Prop} (hnil : motive [])
    (hsnoc : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) :
    ∀ l : List α, motive l := by
  have aux : ∀ r : List α, motive r.reverse := by
    intro r
    induction r with
    | nil => exact hnil
    | cons x xs ih =>
        have := hsnoc xs.reverse x ih
        simpa [List.reverse_cons] using this
  intro l
  simpa using aux l.reverse

theorem pow17_pos (n : Nat) : 0 < 17 ^ n := by
  induction n with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ]; omega

/-! ## Basic facts about `symbolCode` -/

theorem symbolCode_lt (s : L) : symbolCode s < 17 := by
  cases s <;> decide

theorem codeSymbol_symbolCode (s : L) : codeSymbol (symbolCode s) = some s := by
  cases s <;> rfl

/-! ## `encodeL` -/

/-- The base-17 Horner fold, with an arbitrary starting accumulator. -/
theorem foldl17_acc (l : L_formula) (acc : Nat) :
    List.foldl (fun acc sym => acc * 17 + symbolCode sym) acc l
      = acc * 17 ^ l.length + encodeL l := by
  induction l generalizing acc with
  | nil => simp [encodeL]
  | cons a t ih =>
      have h0 : encodeL (a :: t)
          = List.foldl (fun acc sym => acc * 17 + symbolCode sym) (symbolCode a) t := by
        simp [encodeL]
      rw [List.foldl_cons, ih, h0, ih, List.length_cons, Nat.pow_succ]
      generalize 17 ^ t.length = p
      have e1 : (acc * 17 + symbolCode a) * p = acc * (p * 17) + symbolCode a * p := by
        rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 17 p]
      omega

theorem encodeL_append (l₁ l₂ : L_formula) :
    encodeL (l₁ ++ l₂) = encodeL l₁ * 17 ^ l₂.length + encodeL l₂ := by
  have h : encodeL (l₁ ++ l₂)
      = List.foldl (fun acc sym => acc * 17 + symbolCode sym) (encodeL l₁) l₂ := by
    simp [encodeL, List.foldl_append]
  rw [h, foldl17_acc]

theorem encodeL_nil : encodeL [] = 0 := rfl

theorem encodeL_singleton (a : L) : encodeL [a] = symbolCode a := by
  simp [encodeL]

theorem encodeL_cons (a : L) (l : L_formula) :
    encodeL (a :: l) = symbolCode a * 17 ^ l.length + encodeL l := by
  have h := encodeL_append [a] l
  rw [encodeL_singleton] at h
  exact h

theorem encodeL_snoc (l : L_formula) (a : L) :
    encodeL (l ++ [a]) = encodeL l * 17 + symbolCode a := by
  have h := encodeL_append l [a]
  have hl : ([a] : L_formula).length = 1 := rfl
  rw [encodeL_singleton, hl, Nat.pow_one] at h
  exact h

theorem encodeL_lt (l : L_formula) : encodeL l < 17 ^ l.length := by
  induction l with
  | nil => decide
  | cons a t ih =>
      rw [encodeL_cons, List.length_cons, Nat.pow_succ]
      have hc : symbolCode a < 17 := symbolCode_lt a
      have hle : symbolCode a * 17 ^ t.length ≤ 16 * 17 ^ t.length :=
        Nat.mul_le_mul (by omega) (Nat.le_refl _)
      generalize hp : 17 ^ t.length = p at *
      omega

theorem le_encodeL {a : L} (l : L_formula) (h : symbolCode a ≠ 0) :
    17 ^ l.length ≤ encodeL (a :: l) := by
  rw [encodeL_cons]
  have hle : 1 * 17 ^ l.length ≤ symbolCode a * 17 ^ l.length :=
    Nat.mul_le_mul (by omega) (Nat.le_refl _)
  omega

theorem encodeL_cons_pos {a : L} (l : L_formula) (h : symbolCode a ≠ 0) :
    0 < encodeL (a :: l) := by
  have h1 := le_encodeL l h
  have h2 := pow17_pos l.length
  omega

/-! ## `digits17L` -/

theorem digits17Helper_zero : digits17Helper 0 = [] := by
  rw [digits17Helper]

theorem digits17Helper_succ (k : Nat) :
    digits17Helper (k + 1) = digits17Helper ((k + 1) / 17) ++ [(k + 1) % 17] := by
  rw [digits17Helper]

theorem digits17L_of_pos {n : Nat} (h : 0 < n) : digits17L n = digits17Helper n := by
  cases n with
  | zero => omega
  | succ k => rfl

/-- A single nonzero base-17 digit is its own digit expansion. -/
theorem digits17L_of_lt {c : Nat} (h0 : c ≠ 0) (h : c < 17) : digits17L c = [c] := by
  cases c with
  | zero => omega
  | succ k =>
      rw [digits17L_of_pos (by omega), digits17Helper_succ]
      have hd : (k + 1) / 17 = 0 := by omega
      have hm : (k + 1) % 17 = k + 1 := by omega
      rw [hd, hm, digits17Helper_zero, List.nil_append]

/-- Appending one digit on the right. -/
theorem digits17L_mul_add {N c : Nat} (hN : 0 < N) (hc : c < 17) :
    digits17L (N * 17 + c) = digits17L N ++ [c] := by
  have hpos : 0 < N * 17 + c := by omega
  cases hM : N * 17 + c with
  | zero => omega
  | succ k =>
      rw [digits17L_of_pos (by omega), digits17Helper_succ]
      have hd : (k + 1) / 17 = N := by omega
      have hm : (k + 1) % 17 = c := by omega
      rw [hd, hm, digits17L_of_pos hN]

/-- The key digits round-trip: a code word whose first symbol has a nonzero
    code has exactly the expected base-17 digits. -/
theorem digits17_encodeL (a : L) (l : L_formula) (h : symbolCode a ≠ 0) :
    digits17L (encodeL (a :: l)) = (a :: l).map symbolCode := by
  induction l using list_rev_rec with
  | hnil =>
      rw [encodeL_singleton, digits17L_of_lt h (symbolCode_lt a)]
      simp
  | hsnoc t b ih =>
      have hcons : a :: (t ++ [b]) = (a :: t) ++ [b] := by simp
      rw [hcons, encodeL_snoc]
      rw [digits17L_mul_add (encodeL_cons_pos t h) (symbolCode_lt b), ih]
      simp

/-! ## `decodeDigitsL` -/

theorem decodeDigitsL_map (l : L_formula) :
    decodeDigitsL (l.map symbolCode) = some l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [List.map_cons, decodeDigitsL, codeSymbol_symbolCode, ih]
      rfl

/-! ## Heads of unparsed strings -/

theorem unparse_term_head (t : Term) :
    ∃ a l, unparse_term t = a :: l ∧ symbolCode a ≠ 0 := by
  induction t with
  | var n => exact ⟨L.var, List.replicate n L.prime, rfl, by decide⟩
  | zero => exact ⟨L.O, [], rfl, by decide⟩
  | succ t ih =>
      obtain ⟨a, l, hu, hc⟩ := ih
      refine ⟨a, l ++ [L.S], ?_, hc⟩
      simp only [unparse_term, hu, List.cons_append]
  | add m n _ _ => exact ⟨L.l_par, _, rfl, by decide⟩
  | mul m n _ _ => exact ⟨L.l_par, _, rfl, by decide⟩
  | exp m n _ _ => exact ⟨L.l_par, _, rfl, by decide⟩

theorem unparse_head_code_ne_zero (φ : Formula) :
    ∃ a l, unparse φ = a :: l ∧ symbolCode a ≠ 0 := by
  cases φ with
  | eq m n =>
      obtain ⟨a, l, hu, hc⟩ := unparse_term_head m
      exact ⟨a, l ++ L.eq :: unparse_term n, by simp only [unparse, hu, List.cons_append], hc⟩
  | le m n =>
      obtain ⟨a, l, hu, hc⟩ := unparse_term_head m
      exact ⟨a, l ++ L.leq :: unparse_term n, by simp only [unparse, hu, List.cons_append], hc⟩
  | not p => exact ⟨L.not, _, rfl, by decide⟩
  | and p q => exact ⟨L.l_par, _, rfl, by decide⟩
  | or p q => exact ⟨L.l_par, _, rfl, by decide⟩
  | imp p q => exact ⟨L.l_par, _, rfl, by decide⟩
  | forall_ n p => exact ⟨L.all, _, rfl, by decide⟩
  | exists_ n p => exact ⟨L.exi, _, rfl, by decide⟩

/-! ## The round-trip -/

theorem decodeL_encode (φ : Formula) : decodeL (encode φ) = some (unparse φ) := by
  obtain ⟨a, l, hu, hc⟩ := unparse_head_code_ne_zero φ
  show decodeDigitsL (digits17L (encodeL (unparse φ))) = some (unparse φ)
  rw [hu, digits17_encodeL a l hc, decodeDigitsL_map]

theorem decode_encode (φ : Formula) : ∃ fuel, decode fuel (encode φ) = some φ := by
  obtain ⟨fuel, hf⟩ := unparse_parse_id φ
  refine ⟨fuel, ?_⟩
  show (match decodeL (encode φ) with
        | some xs => match parse fuel xs with
                     | some ψ => some ψ
                     | _ => none
        | none => none) = some φ
  rw [decodeL_encode]
  show (match parse fuel (unparse φ) with
        | some ψ => some ψ
        | _ => none) = some φ
  rw [hf]

/-! ## Numerals -/

theorem unparse_term_of_nat (n : Nat) :
    unparse_term (term_of_nat n) = L.O :: List.replicate n L.S := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show unparse_term (term_of_nat k) ++ [L.S] = _
      rw [ih, List.replicate_succ' (n := k) (a := L.S)]
      simp

theorem encodeL_replicate_S (n : Nat) : encodeL (List.replicate n L.S) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, encodeL_cons, ih]
      simp

theorem length_replicate_S (n : Nat) : (List.replicate n L.S).length = n := by
  simp

