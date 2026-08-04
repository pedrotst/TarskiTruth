import Tarski.Model
import Tarski.EncodingLemmas

open Lang
open Godel
open Env

/-!
# Phase 4 — the diagonal relation is arithmetic

`diagonalR n m` says: `k` is the base-17 digit length of `n`, and
`m = diagF n k`.  See `Tarski/GodelEncoding.lean` for the derivation.
-/

/-- The numeral `17`, as an object-language term. -/
def t17 : Term := term_of_nat 17

/-- The object-language term denoting `diagF v₀ v₂` with `v₀ = n`, `v₂ = k`. -/
def diagFTerm : Term :=
  let c := term_of_nat diagC
  let s := t17
  let t1 := Term.mul c (.exp s (.var 0))
  let t2 := Term.add (.mul t1 s) (term_of_nat 14)
  let t3 := Term.add (.mul t2 (.exp s (.var 2))) (.var 0)
  let t4 := Term.add (.mul t3 s) (term_of_nat 10)
  Term.add (.mul t4 s) (term_of_nat 10)

/-- The object-language formula defining `diagonalR` on variables `0` (= `n`)
and `1` (= `m`), with `2` bound as the digit length. -/
def diagFormula : Formula :=
  .exists_ 2
    (.and (.le (.succ (.var 0)) (.exp t17 (.var 2)))
      (.and (.le (.exp t17 (.var 2)) (.mul t17 (.var 0)))
        (.eq (.var 1) diagFTerm)))

theorem diagonalR_arith :
  IsArithmeticRel2 diagonalR := by
  sorry

theorem diagonalR_functional :
  diagonalR n m₁ →
  diagonalR n m₂ →
  m₁ = m₂ := by
  sorry

theorem diagonalR_encode :
  ∀ ψ, diagonalR (encode ψ) (encode (diagSentence ψ)) := by
  sorry
