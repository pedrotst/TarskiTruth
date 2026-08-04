import Tarski.Model

open Lang
open Env

/-!
# Phase 5a — coincidence lemma and the `0 ↔ 1` variable swap
-/

theorem eval_coincide (φ : Formula) (σ σ' : Assignment)
    (h : ∀ x ∈ fv φ, σ x = σ' x) :
    (evalFormula σ φ ↔ evalFormula σ' φ) := by
  sorry

def swapNat (x : Nat) : Nat := if x = 0 then 1 else if x = 1 then 0 else x

def swapTerm : Term → Term
  | .var v => .var (swapNat v)
  | .zero => .zero
  | .succ t => .succ (swapTerm t)
  | .add a b => .add (swapTerm a) (swapTerm b)
  | .mul a b => .mul (swapTerm a) (swapTerm b)
  | .exp a b => .exp (swapTerm a) (swapTerm b)

def swap01 : Formula → Formula
  | .eq a b => .eq (swapTerm a) (swapTerm b)
  | .le a b => .le (swapTerm a) (swapTerm b)
  | .not p => .not (swap01 p)
  | .and p q => .and (swap01 p) (swap01 q)
  | .or p q => .or (swap01 p) (swap01 q)
  | .imp p q => .imp (swap01 p) (swap01 q)
  | .forall_ n p => .forall_ (swapNat n) (swap01 p)
  | .exists_ n p => .exists_ (swapNat n) (swap01 p)

theorem eval_swap (φ : Formula) (σ : Assignment) :
    evalFormula σ (swap01 φ) ↔ evalFormula (σ ∘ swapNat) φ := by
  sorry

theorem fv_swap (φ : Formula) (x : Nat) :
    x ∈ fv (swap01 φ) ↔ swapNat x ∈ fv φ := by
  sorry
