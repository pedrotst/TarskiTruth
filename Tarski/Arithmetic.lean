import Tarski.Lang
import Tarski.GodelEncoding
import Tarski.Environment

open Std
open Lang
open Godel
open Env

structure ArithmeticStructure where
  zero : Nat
  succ : Nat → Nat
  add  : Nat → Nat → Nat
  mul  : Nat → Nat → Nat
  exp  : Nat → Nat → Nat
  le   : Nat → Nat → Prop

-- The Model
@[simp]
def M : ArithmeticStructure where
  zero := 0
  succ := Nat.succ
  add := Nat.add
  mul := Nat.mul
  exp := Nat.pow
  le := (· ≤ ·)

@[simp]
def evalTerm (σ : Assignment) : Term → Nat
  | .var v => σ v
  | .zero => M.zero
  | .succ n => M.succ (evalTerm σ n)
  | .add t s => M.add (evalTerm σ t) (evalTerm σ s)
  | .mul t s => M.mul (evalTerm σ t) (evalTerm σ s)
  | .exp t s => M.exp (evalTerm σ t) (evalTerm σ s)

@[simp]
def evalFormula (σ : Assignment) : Formula → Prop
  | .eq t s      => evalTerm σ t = evalTerm σ s
  | .le t s      => M.le (evalTerm σ t) (evalTerm σ s)
  | .not φ       => ¬ evalFormula σ φ
  | .and φ ψ     => evalFormula σ φ ∧ evalFormula σ ψ
  | .or φ ψ      => evalFormula σ φ ∨ evalFormula σ ψ
  | .imp φ ψ     => evalFormula σ φ → evalFormula σ ψ
  | .forall_ x φ => ∀ n : Nat, evalFormula (update σ x n) φ
  | .exists_ x φ => ∃ n : Nat, evalFormula (update σ x n) φ

example (σ : Assignment) : evalFormula σ reflLe := by
  intro n
  exact Nat.le_refl n

example (σ : Assignment) : evalFormula σ (.forall_ 0 (.exists_ 1 (.not (.eq (.var 0) (.var 1))))) := by
  intros n
  exists (n + 1)
  simp []


@[simp]
def ExpressesSet
  (φ : Formula)
  (S : Nat → Prop) : Prop :=
  only_free_var_zero φ ∧
  ∀ n, (evalFormula empty_ctx (subst (term_of_nat n) φ)) ↔ S n

def IsArithmeticSet
    (S : Nat → Prop) : Prop :=
  ∃ φ, ExpressesSet φ S

@[simp]
def ExpressesRel2
    (φ : Formula)
    (R : Nat → Nat → Prop) : Prop :=
  only_free_var_zero_one φ ∧
  ∀ m n,
    evalFormula
    (fun x =>
        if x = 0 then m
        else if x = 1 then n
        else 0) φ
    ↔ R m n

def IsArithmeticRel2
    (R : Nat → Nat → Prop) : Prop :=
  ∃ φ, ExpressesRel2 φ R

example :
  ExpressesRel2 ltFormula (· < ·) := by
  unfold ExpressesRel2
  constructor
  · unfold ltFormula
    simp [only_free_var_zero_one, fv, fv_term]
  intros m n
  constructor <;> simp <;> grind

#eval decode 0 0

example :
  p = (.eq (.var 0) (.var 1)) →
  q = (.eq (.var 1) (.var 0)) →
  evalFormula σ (.and (.imp p q) (.imp q p)) := by
  intros h1 h2
  rw [h1, h2]
  simp
  constructor <;> grind

#eval parseFormula 1 [L.S]

@[simp]
theorem parseQuantifier0_none :
forall n,
  parseFormula.parseQuantifier n [L.S] = none := by
  intro n
  cases n with
  | zero => simp
  | succ n =>
    simp

theorem term_of_nat_sound n:
  forall σ, evalTerm σ (term_of_nat n) = n := by
  intros
  induction n <;> simp [term_of_nat]
  assumption


theorem evalTerm_subst_update :
  forall t σ n,
    evalTerm σ (substTerm (term_of_nat n) t)
      = evalTerm (update σ 0 n) t := by
  intro t
  induction t with
  | var n =>
    by_cases h : n = 0
    · simp [h, term_of_nat_sound]
    · simp [h]
  | zero => simp []
  | succ n ih => simp [ih]
  | exp m n ih1 ih2 => simp [ih1, ih2]
  | mul m n ih1 ih2 => simp [ih1, ih2]
  | add m n ih1 ih2 => simp [ih1, ih2]

theorem closed_term_of_nat :
  forall n, closed_term (term_of_nat n) := by
  intro n
  induction n with
  | zero => simp [closed_term, term_of_nat, fv_term]
  | succ n ih =>
    simp [closed_term, term_of_nat, fv_term] at *
    assumption


theorem evalFormula_subst_update :
  forall φ σ n,
  evalFormula σ (subst (term_of_nat n) φ)
            = evalFormula (update σ 0 n) φ := by
  intro φ
  induction φ with
  | eq p q =>
    intro σ n
    simp
    repeat rw [evalTerm_subst_update]
  | le p q =>
    intro σ n
    simp
    repeat rw [evalTerm_subst_update]
  | and p q ih1 ih2 =>
    simp
    grind
  | or p q ih1 ih2 =>
    simp
    grind
  | not p ih =>
    simp
    grind
  | imp p q ih1 ih2 =>
    simp
    grind
  | forall_ x p ih =>
    intros σ n
    have h : closed_term (term_of_nat n) := closed_term_of_nat n
    simp
    by_cases hx : x = 0
    · simp [hx]
    · simp [hx]
      constructor
      · intro h1 n1
        specialize ih (update σ x n1) n
        specialize h1 n1
        rw [ih] at h1
        simp [env_comm hx] at h1
        assumption
      · intro h1 n1
        specialize ih (update σ x n1) n
        rw [ih]
        rw [env_comm hx]
        apply h1
  | exists_ x p ih =>
    intros σ n
    have h : closed_term (term_of_nat n) := closed_term_of_nat n
    simp
    by_cases hx : x = 0
    · simp [hx]
    · simp [hx]
      constructor
      · intro h1
        rcases h1 with ⟨n1, h1⟩
        exists n1
        specialize ih (update σ x n1) n
        rw [ih] at h1
        simp [env_comm hx] at h1
        assumption
      · intro h1
        rcases h1 with ⟨n1, h1⟩
        exists n1
        specialize ih (update σ x n1) n
        rw [ih]
        rw [env_comm hx]
        assumption

theorem diagonal_soundness :
forall φₙ n σ,
  evalFormula σ (subst (term_of_nat n) φₙ)
    = evalFormula σ (.forall_ 0 (.imp (.eq (.var 0) (term_of_nat n)) φₙ)) := by
  intro φₙ n σ
  rw [evalFormula_subst_update φₙ σ n]
  simp [term_of_nat_sound]

-- The following proof is still in progress and has been deferred
-- to keep the file syntactically valid.
theorem diagonalR_arith:
  IsArithmeticRel2 diagonalR := by
  rw [IsArithmeticRel2]
  exists (reflLe)
  unfold ExpressesRel2
  intros m n
  constructor
  · intro h
    sorry
  · sorry

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


-- The following proofs are still in progress and have been deferred
-- to keep the file syntactically valid.
theorem star_arithmetic :
  IsArithmeticSet S → IsArithmeticSet (star S) := by
  intro h
  rcases h with ⟨φ, h⟩
  have h1 := diagonalR_arith
  rcases h1 with ⟨ψ, h2⟩
  unfold IsArithmeticSet
  exists ψ

  unfold ExpressesSet
  rw [ExpressesRel2] at h2
  intro n
  unfold star
  specialize h2 n 0
  sorry

theorem encode_decode_unique :
  (exists fuel, decode fuel ⌜φ⌝ = some ψ) →
    ψ = φ := by
    sorry

theorem ex p (P : Nat → Prop):
  (∃ m, diagonalR p m → P m) = (exists m fuel, diagonal_formula fuel p = some m → P (encode m))
  := by
  sorry

theorem ex1 :
(∃ m fuel, diagonal_formula fuel ⌜ψ⌝ = some m → ¬T ⌜m⌝)
= (forall m, exists φ fuel, decode fuel ⌜m⌝ = some φ → ¬ T ⌜(.forall_ 0 (.imp (.eq (.var 0) (.var m)) φ))⌝) :=
by sorry

theorem no_self_negation (P : Prop) :
    ¬ (P ↔ ¬ P) := by
  intro h
  have hnP : ¬ P := by
    intro hp
    exact h.mp hp hp
  exact hnP (h.mpr hnP)

-- theorem tarski:
--   ¬ IsArithmeticSet T := by
--   intro h
--   have h1 := negSet_arith _ h
--   have h2 := star_arithmetic h1
--   have h3 := h1
--   unfold IsArithmeticSet at h2
--   rcases h2 with ⟨ψ, h2⟩
--   unfold ExpressesSet at h2
--   rcases h2 with ⟨h4, h2⟩
--   let g := ⌜ ψ ⌝
--   specialize (h2 g)
--   unfold star at h2
--   unfold negSet at *
--   unfold diagonalR at h2
--   unfold diagonal at h2
--   unfold diagonal_formula at h2
--   have contr : evalFormula empty_ctx (subst (term_of_nat g) ψ)
--               ↔ ¬ evalFormula empty_ctx (subst (term_of_nat g) ψ) := by
--     calc
--       evalFormula empty_ctx (subst (term_of_nat ⌜ψ⌝) ψ)
--         ↔ ∃ m, diagonalR ⌜ψ⌝ m → ¬ T m := h2
--       _ ↔ diagonalR ⌜ψ⌝ 0 → ¬ T 0 := by sorry
--       _ ↔ ¬ evalFormula empty_ctx (subst (term_of_nat ⌜ψ⌝) ψ) := by sorry
--   grind
theorem diagonalR_encode :
  ∀ ψ, diagonalR (encode ψ) (encode (diagSentence ψ)) := by
  sorry

theorem diagonalR_functional :
  diagonalR n m₁ →
  diagonalR n m₂ →
  m₁ = m₂ := by
  sorry

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











-- def IsArithmeticRel2
--     (R : Nat → Nat → Prop) : Prop :=
--   ∃ φ, ExpressesRel2 φ R
