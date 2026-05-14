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
  ∀ n, (evalFormula empty_ctx (subst (term_of_nat n) φ)) ↔ S n

def IsArithmeticSet
    (S : Nat → Prop) : Prop :=
  ∃ φ, ExpressesSet φ S

@[simp]
def ExpressesRel2
    (φ : Formula)
    (R : Nat → Nat → Prop) : Prop :=
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
  exists fuel φ, decode fuel n = some φ →
  evalFormula empty_ctx φ

def star (S : Nat → Prop) : Nat → Prop := fun n =>
  exists m, diagonalR n m → S m

def negSet (S : Nat → Prop) : Nat → Prop := fun n =>
  ¬ S n

theorem negSet_arith S :
  IsArithmeticSet S → IsArithmeticSet (negSet S) := by
  intro h
  unfold IsArithmeticSet at *
  rcases h with ⟨φ, h⟩
  exists (.not φ )
  simp at *
  intro n
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

theorem encode_decode_idem :
  (exists fuel, decode fuel ⌜ψ⌝ = some p) →
    p = ψ := by
    sorry

theorem ex p (P : Nat → Prop):
  (∃ m, diagonalR p m → P m) = (exists m fuel, diagonal_formula fuel p = some m → P (encode m))
  := by
  sorry

theorem ex1 :
(∃ m fuel, diagonal_formula fuel ⌜ψ⌝ = some m → ¬T ⌜m⌝)
= (forall m, exists φ fuel, decode fuel ⌜m⌝ = some φ → ¬ T ⌜(.forall_ 0 (.imp (.eq (.var 0) (.var m)) φ))⌝) :=
by sorry

theorem tarski:
  ¬ IsArithmeticSet T := by
  intro h
  have h1 := negSet_arith _ h
  have h2 := star_arithmetic h1
  have h3 := h1
  unfold IsArithmeticSet at h2
  rcases h2 with ⟨ψ, h2⟩
  unfold ExpressesSet at h2
  specialize (h2 (encode ψ))
  unfold star at h2
  unfold negSet at *
  have contr : evalFormula empty_ctx (subst ψ (term_of_nat ⌜ψ⌝))
              ↔ ¬ evalFormula empty_ctx (subst ψ (term_of_nat ⌜ψ⌝)) := by
    calc
      evalFormula empty_ctx (subst ψ (term_of_nat ⌜ψ⌝))
        ↔ ∃ m, diagonalR ⌜ψ⌝ m → ¬ T m := h2
      _ ↔ diagonalR ⌜ψ⌝ 0 → ¬ T 0 := by
        constructor
        · intro h
          rcases h with ⟨m, h⟩
          rw [diagonalR] at h
          intro h1
          intro
          apply h
          unfold diagonal
          exists 100

      _ ↔ ¬ evalFormula empty_ctx (subst ψ (term_of_nat ⌜ψ⌝)) := by sorry
  grind












-- def IsArithmeticRel2
--     (R : Nat → Nat → Prop) : Prop :=
--   ∃ φ, ExpressesRel2 φ R
