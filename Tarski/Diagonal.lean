import Tarski.Model
import Tarski.EncodingLemmas

open Lang
open Godel
open Env

/-!
# Phase 4 — the diagonal relation is arithmetic

`diagonalR n m` says: `k` is the base-17 digit length of `n`, and
`m = diagF n k`.  See `Tarski/GodelEncoding.lean` for the derivation of the
polynomial.

**Gotcha.**  `term_of_nat diagC` is a unary numeral with ~3.7e8 constructors.
Any tactic that puts `fv_term` or `evalTerm` into a simp set *while such a
numeral is present* produces a proof term the kernel then tries to evaluate,
which hangs.  So everything below is stated for **abstract** term parameters
`c s a14 a10`, with their `fv_term` / `evalTerm` values supplied as hypotheses;
the concrete numerals are only ever substituted at the very end, via
`closed_term_of_nat` and `term_of_nat_sound`.
-/

/-! ## Base-17 digit length is unique -/

theorem digitLen17_unique {n k k' : Nat}
    (h : isDigitLen17 n k) (h' : isDigitLen17 n k') : k = k' := by
  obtain ⟨hlt, hle⟩ := h
  obtain ⟨hlt', hle'⟩ := h'
  rcases Nat.lt_trichotomy k k' with hk | hk | hk
  · exfalso
    have h1 : 17 ^ (k + 1) ≤ 17 ^ k' :=
      Nat.pow_le_pow_right (by omega) (by omega : k + 1 ≤ k')
    have h3 : (17 : Nat) ^ (k + 1) = 17 ^ k * 17 := Nat.pow_succ 17 k
    omega
  · exact hk
  · exfalso
    have h1 : 17 ^ (k' + 1) ≤ 17 ^ k :=
      Nat.pow_le_pow_right (by omega) (by omega : k' + 1 ≤ k)
    have h3 : (17 : Nat) ^ (k' + 1) = 17 ^ k' * 17 := Nat.pow_succ 17 k'
    omega

theorem diagonalR_functional :
  diagonalR n m₁ →
  diagonalR n m₂ →
  m₁ = m₂ := by
  rintro ⟨k, hk, rfl⟩ ⟨k', hk', rfl⟩
  rw [digitLen17_unique hk hk']

/-! ## The defining formula, with abstract numerals -/

/-- `((((c * s^v₀) * s + a14) * s^v₂ + v₀) * s + a10) * s + a10`. -/
def diagFTermG (c s a14 a10 : Term) : Term :=
  .add
    (.mul
      (.add
        (.mul
          (.add
            (.mul (.add (.mul (.mul c (.exp s (.var 0))) s) a14) (.exp s (.var 2)))
            (.var 0))
          s)
        a10)
      s)
    a10

/-- `∃v₂. v₀ < s^v₂ ∧ s^v₂ ≤ s·v₀ ∧ v₁ = diagFTermG …`. -/
def diagFormulaG (c s a14 a10 : Term) : Formula :=
  .exists_ 2
    (.and (.le (.succ (.var 0)) (.exp s (.var 2)))
      (.and (.le (.exp s (.var 2)) (.mul s (.var 0)))
        (.eq (.var 1) (diagFTermG c s a14 a10))))

theorem fv_diagFormulaG {c s a14 a10 : Term}
    (hc : fv_term c = []) (hs : fv_term s = [])
    (h14 : fv_term a14 = []) (h10 : fv_term a10 = [])
    (x : Nat) (hx : x ∈ fv (diagFormulaG c s a14 a10)) : x = 0 ∨ x = 1 := by
  simp [diagFormulaG, diagFTermG, fv, fv_term, hc, hs, h14, h10] at hx
  rcases hx with h | h | h <;> simp [h]

theorem eval_diagFormulaG (σ : Assignment) {c s a14 a10 : Term}
    (hc : ∀ τ, evalTerm τ c = diagC) (hs : ∀ τ, evalTerm τ s = 17)
    (h14 : ∀ τ, evalTerm τ a14 = 14) (h10 : ∀ τ, evalTerm τ a10 = 10) :
    (evalFormula σ (diagFormulaG c s a14 a10) ↔ diagonalR (σ 0) (σ 1)) := by
  simp [diagFormulaG, diagFTermG, hc, hs, h14, h10, diagonalR, isDigitLen17, diagF]
  constructor
  · rintro ⟨k, h1, h2, h3⟩
    exact ⟨k, ⟨h1, h2⟩, h3⟩
  · rintro ⟨k, ⟨h1, h2⟩, h3⟩
    exact ⟨k, h1, h2, h3⟩

/-! ## The concrete formula -/

/-- The numeral `17`, as an object-language term. -/
def t17 : Term := term_of_nat 17

def diagFormula : Formula :=
  diagFormulaG (term_of_nat diagC) t17 (term_of_nat 14) (term_of_nat 10)

theorem only_free_diagFormula : only_free_var_zero_one diagFormula := by
  intro x hx
  exact fv_diagFormulaG (closed_term_of_nat diagC) (closed_term_of_nat 17)
    (closed_term_of_nat 14) (closed_term_of_nat 10) x hx

theorem diagonalR_arith :
  IsArithmeticRel2 diagonalR := by
  refine ⟨diagFormula, only_free_diagFormula, ?_⟩
  intro m n
  have h := eval_diagFormulaG
      (σ := fun x => if x = 0 then m else if x = 1 then n else 0)
      (c := term_of_nat diagC) (s := t17) (a14 := term_of_nat 14) (a10 := term_of_nat 10)
      (fun τ => term_of_nat_sound diagC τ) (fun τ => term_of_nat_sound 17 τ)
      (fun τ => term_of_nat_sound 14 τ) (fun τ => term_of_nat_sound 10 τ)
  simpa [diagFormula] using h

/-! ## `diagonalR` sends `⌜ψ⌝` to `⌜diagSentence ψ⌝` -/

theorem diagonalR_encode :
  ∀ ψ, diagonalR (encode ψ) (encode (diagSentence ψ)) := by
  sorry
