import Tarski.Model
import Tarski.Diagonal
import Tarski.Semantics

open Std
open Lang
open Godel
open Env

def T (n: Nat) : Prop :=
  exists fuel φ, decode fuel n = some φ ∧
  closed φ ∧
  evalFormula empty_ctx φ

def star (S : Nat → Prop) : Nat → Prop := fun n =>
  exists m, diagonalR n m ∧ S m

def negSet (S : Nat → Prop) : Nat → Prop := fun n =>
  ¬ S n

theorem only_free_var_neg:
  forall φ,
  only_free_var_zero φ →
  only_free_var_zero φ.not := by
  intro φ h
  induction φ
  all_goals
    unfold only_free_var_zero at *
    intro h1 h2
    simp [fv] at *
    apply h
    try assumption
  all_goals
    try rcases h2 with ⟨h2_1, h2_2⟩ <;> assumption


theorem negSet_arith S :
  IsArithmeticSet S → IsArithmeticSet (negSet S) := by
  intro h
  unfold IsArithmeticSet at *
  rcases h with ⟨φ, h⟩
  exists (.not φ )
  simp at *
  rcases h with ⟨h1, h⟩
  constructor
  · exact only_free_var_neg _ h1
  · intro n
    specialize h n
    constructor
    · intro h1
      simp [negSet]
      grind
    · simp [negSet]
      intro h1
      grind


theorem star_arithmetic :
  IsArithmeticSet S → IsArithmeticSet (star S) := by
  sorry

theorem no_self_negation (P : Prop) :
    ¬ (P ↔ ¬ P) := by
  intro h
  have hnP : ¬ P := by
    intro hp
    exact h.mp hp hp
  exact hnP (h.mpr hnP)

theorem T_encode_closed :
  closed φ →
  (T (encode φ) ↔ evalFormula empty_ctx φ) := by
  sorry

theorem diagSentence_closed :
  ExpressesSet ψ S →
  closed (diagSentence ψ) := by
  intro h
  unfold ExpressesSet at h
  rcases h with ⟨h1, h⟩
  unfold diagSentence
  unfold diagAt
  unfold closed
  have h2 := closed_term_of_nat
  -- specialize h2 ⌜ψ⌝
  unfold closed_term at h2
  simp [-encode, fv]
  constructor
  · intros a h
    simp [fv_term] at h
    assumption
  · constructor
    · intros a h3
      specialize h2 ⌜ψ⌝
      exfalso
      grind
    · unfold only_free_var_zero at h1
      assumption

theorem tarski :
  ¬ IsArithmeticSet T := by
  intro hT

  -- Since T is arithmetic, its complement is arithmetic.
  have hnegT : IsArithmeticSet (negSet T) := by
    exact negSet_arith T hT

  -- Since ¬T is arithmetic, its diagonal/star preimage is arithmetic.
  have hstarNegT : IsArithmeticSet (star (negSet T)) := by
    exact star_arithmetic hnegT

  -- Choose ψ expressing star (negSet T).
  rcases hstarNegT with ⟨ψ, hψ⟩

  let g : Nat := encode ψ
  let δ : Formula := diagSentence ψ
  let P : Prop := evalFormula empty_ctx (subst (term_of_nat g) ψ)

  -- ψ(g) expresses: g ∈ star (negSet T).
  have hψg :
      P ↔ star (negSet T) g := by
    dsimp [P, g]
    exact hψ.2 g

  -- The diagonal relation sends g to the code of δ.
  have hdiagR :
      diagonalR g (encode δ) := by
    dsimp [g, δ, diagSentence]
    exact diagonalR_encode ψ
    -- HOLE:
    -- theorem diagonalR_encode :
    --   ∀ ψ, diagonalR (encode ψ) (encode (diagSentence ψ))

  -- The diagonal relation is functional.
  have hdiag_fun :
      ∀ m, diagonalR g m → m = encode δ := by
    intro m hm
    exact diagonalR_functional hm hdiagR
    -- HOLE:
    -- theorem diagonalR_functional :
    --   diagonalR n m₁ → diagonalR n m₂ → m₁ = m₂

  -- Therefore star (negSet T) g is equivalent to ¬ T (encode δ).
  have hstar_eq :
      star (negSet T) g ↔ ¬ T (encode δ) := by
    constructor
    · intro hs
      rcases hs with ⟨m, hm_diag, hm_negT⟩
      have hm : m = encode δ := hdiag_fun m hm_diag
      simpa [negSet, hm] using hm_negT

    · intro hnotT
      exact ⟨encode δ, hdiagR, by simpa [negSet] using hnotT⟩

  -- Your diagonal soundness theorem:
  -- ψ(g) has the same truth value as the diagonal sentence δ.
  have hdiag_sound :
      P ↔ evalFormula empty_ctx δ :=
    Iff.of_eq (diagonal_soundness ψ (encode ψ) empty_ctx)

  have δ_closed : closed δ := diagSentence_closed hψ

  -- Truth of the Gödel number of δ agrees with semantic truth of δ.
  have hTδ :
      T (encode δ) ↔ evalFormula empty_ctx δ := T_encode_closed δ_closed

    -- HOLE:
    -- theorem T_encode_closed :
    --   closed δ →
    --   T (encode δ) ↔ evalFormula empty_ctx δ

  -- If `T_encode_closed` needs closedness first, move this above hTδ.

  -- Combine the equivalences:
  -- P ↔ star (¬T) g
  --   ↔ ¬ T ⌜δ⌝
  --   ↔ ¬ eval δ
  --   ↔ ¬ P
  have hP_notP :
      P ↔ ¬ P := by
    calc
      P
          ↔ star (negSet T) g := hψg
      _   ↔ ¬ T (encode δ) := hstar_eq
      _   ↔ ¬ evalFormula empty_ctx δ := by
              constructor
              · intro hnotT hδ
                exact hnotT ((hTδ.mpr hδ))
              · intro hnotδ hTcode
                exact hnotδ ((hTδ.mp hTcode))
      _   ↔ ¬ P := by
              constructor
              · intro hnotδ hp
                exact hnotδ (hdiag_sound.mp hp)
              · intro hnotP hδ
                exact hnotP (hdiag_sound.mpr hδ)

  exact no_self_negation P hP_notP
