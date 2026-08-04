import Tarski.Model

open Lang
open Env

/-!
# Phase 5a — coincidence lemma and the `0 ↔ 1` variable swap

Two pieces of infrastructure needed by `star_arithmetic`:

* `eval_coincide` — truth depends only on the free variables;
* `swap01` — the bijective renaming that exchanges variables `0` and `1`,
  including binders.  Being a bijection it needs no capture side-conditions,
  unlike `subst (.var 1)`.
-/

/-! ## Coincidence -/

theorem evalTerm_coincide : ∀ (t : Term) (σ σ' : Assignment),
    (∀ x ∈ fv_term t, σ x = σ' x) → evalTerm σ t = evalTerm σ' t := by
  intro t
  induction t with
  | var v =>
      intro σ σ' h
      exact h v (by simp [fv_term])
  | zero => intro σ σ' _; rfl
  | succ t ih =>
      intro σ σ' h
      simp [ih σ σ' (fun x hx => h x (by simpa [fv_term] using hx))]
  | add a b iha ihb =>
      intro σ σ' h
      have ha : ∀ x ∈ fv_term a, σ x = σ' x := fun x hx => h x (by simp [fv_term]; exact Or.inl hx)
      have hb : ∀ x ∈ fv_term b, σ x = σ' x := fun x hx => h x (by simp [fv_term]; exact Or.inr hx)
      simp [iha σ σ' ha, ihb σ σ' hb]
  | mul a b iha ihb =>
      intro σ σ' h
      have ha : ∀ x ∈ fv_term a, σ x = σ' x := fun x hx => h x (by simp [fv_term]; exact Or.inl hx)
      have hb : ∀ x ∈ fv_term b, σ x = σ' x := fun x hx => h x (by simp [fv_term]; exact Or.inr hx)
      simp [iha σ σ' ha, ihb σ σ' hb]
  | exp a b iha ihb =>
      intro σ σ' h
      have ha : ∀ x ∈ fv_term a, σ x = σ' x := fun x hx => h x (by simp [fv_term]; exact Or.inl hx)
      have hb : ∀ x ∈ fv_term b, σ x = σ' x := fun x hx => h x (by simp [fv_term]; exact Or.inr hx)
      simp [iha σ σ' ha, ihb σ σ' hb]

theorem eval_coincide : ∀ (φ : Formula) (σ σ' : Assignment),
    (∀ x ∈ fv φ, σ x = σ' x) → (evalFormula σ φ ↔ evalFormula σ' φ) := by
  intro φ
  induction φ with
  | eq a b =>
      intro σ σ' h
      have ha : ∀ x ∈ fv_term a, σ x = σ' x := fun x hx => h x (by simp [fv]; exact Or.inl hx)
      have hb : ∀ x ∈ fv_term b, σ x = σ' x := fun x hx => h x (by simp [fv]; exact Or.inr hx)
      simp [evalTerm_coincide a σ σ' ha, evalTerm_coincide b σ σ' hb]
  | le a b =>
      intro σ σ' h
      have ha : ∀ x ∈ fv_term a, σ x = σ' x := fun x hx => h x (by simp [fv]; exact Or.inl hx)
      have hb : ∀ x ∈ fv_term b, σ x = σ' x := fun x hx => h x (by simp [fv]; exact Or.inr hx)
      simp [evalTerm_coincide a σ σ' ha, evalTerm_coincide b σ σ' hb]
  | not p ih =>
      intro σ σ' h
      simp [ih σ σ' (fun x hx => h x (by simpa [fv] using hx))]
  | and p q ihp ihq =>
      intro σ σ' h
      have hp : ∀ x ∈ fv p, σ x = σ' x := fun x hx => h x (by simp [fv]; exact Or.inl hx)
      have hq : ∀ x ∈ fv q, σ x = σ' x := fun x hx => h x (by simp [fv]; exact Or.inr hx)
      simp [ihp σ σ' hp, ihq σ σ' hq]
  | or p q ihp ihq =>
      intro σ σ' h
      have hp : ∀ x ∈ fv p, σ x = σ' x := fun x hx => h x (by simp [fv]; exact Or.inl hx)
      have hq : ∀ x ∈ fv q, σ x = σ' x := fun x hx => h x (by simp [fv]; exact Or.inr hx)
      simp [ihp σ σ' hp, ihq σ σ' hq]
  | imp p q ihp ihq =>
      intro σ σ' h
      have hp : ∀ x ∈ fv p, σ x = σ' x := fun x hx => h x (by simp [fv]; exact Or.inl hx)
      have hq : ∀ x ∈ fv q, σ x = σ' x := fun x hx => h x (by simp [fv]; exact Or.inr hx)
      simp [ihp σ σ' hp, ihq σ σ' hq]
  | forall_ n p ih =>
      intro σ σ' h
      have key : ∀ v, ∀ x ∈ fv p, (update σ n v) x = (update σ' n v) x := by
        intro v x hx
        by_cases hxn : x = n
        · simp [hxn]
        · have : x ∈ fv (Formula.forall_ n p) := by
            simp [fv, List.mem_filter]
            exact ⟨hx, hxn⟩
          simp [hxn, h x this]
      simp only [evalFormula]
      constructor
      · intro hall v; exact (ih _ _ (key v)).mp (hall v)
      · intro hall v; exact (ih _ _ (key v)).mpr (hall v)
  | exists_ n p ih =>
      intro σ σ' h
      have key : ∀ v, ∀ x ∈ fv p, (update σ n v) x = (update σ' n v) x := by
        intro v x hx
        by_cases hxn : x = n
        · simp [hxn]
        · have : x ∈ fv (Formula.exists_ n p) := by
            simp [fv, List.mem_filter]
            exact ⟨hx, hxn⟩
          simp [hxn, h x this]
      simp only [evalFormula]
      constructor
      · rintro ⟨v, hv⟩; exact ⟨v, (ih _ _ (key v)).mp hv⟩
      · rintro ⟨v, hv⟩; exact ⟨v, (ih _ _ (key v)).mpr hv⟩

/-! ## The `0 ↔ 1` swap -/

def swapNat (x : Nat) : Nat := if x = 0 then 1 else if x = 1 then 0 else x

theorem swapNat_invol (x : Nat) : swapNat (swapNat x) = x := by
  by_cases h0 : x = 0
  · subst h0; rfl
  · by_cases h1 : x = 1
    · subst h1; rfl
    · simp [swapNat, h0, h1]

theorem swapNat_inj {x y : Nat} (h : swapNat x = swapNat y) : x = y := by
  have := congrArg swapNat h
  rwa [swapNat_invol, swapNat_invol] at this

theorem swapNat_eq_iff {x y : Nat} : swapNat x = y ↔ x = swapNat y := by
  constructor
  · intro h; rw [← h, swapNat_invol]
  · intro h; rw [h, swapNat_invol]

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

theorem evalTerm_swap (t : Term) (σ : Assignment) :
    evalTerm σ (swapTerm t) = evalTerm (σ ∘ swapNat) t := by
  induction t <;> simp [swapTerm, Function.comp, *]

theorem update_comp_swap (σ : Assignment) (n v : Nat) :
    (update σ (swapNat n) v) ∘ swapNat = update (σ ∘ swapNat) n v := by
  funext y
  by_cases h : y = n
  · subst h; simp [Function.comp]
  · have hne : swapNat y ≠ swapNat n := fun hc => h (swapNat_inj hc)
    simp [Function.comp, hne, h]

theorem eval_swap : ∀ (φ : Formula) (σ : Assignment),
    (evalFormula σ (swap01 φ) ↔ evalFormula (σ ∘ swapNat) φ) := by
  intro φ
  induction φ with
  | eq a b => intro σ; simp [swap01, evalTerm_swap]
  | le a b => intro σ; simp [swap01, evalTerm_swap]
  | not p ih => intro σ; simp [swap01, ih]
  | and p q ihp ihq => intro σ; simp [swap01, ihp, ihq]
  | or p q ihp ihq => intro σ; simp [swap01, ihp, ihq]
  | imp p q ihp ihq => intro σ; simp [swap01, ihp, ihq]
  | forall_ n p ih =>
      intro σ
      simp only [swap01, evalFormula]
      constructor
      · intro hall v
        have := (ih (update σ (swapNat n) v)).mp (hall v)
        rwa [update_comp_swap] at this
      · intro hall v
        refine (ih (update σ (swapNat n) v)).mpr ?_
        rw [update_comp_swap]
        exact hall v
  | exists_ n p ih =>
      intro σ
      simp only [swap01, evalFormula]
      constructor
      · rintro ⟨v, hv⟩
        refine ⟨v, ?_⟩
        have := (ih (update σ (swapNat n) v)).mp hv
        rwa [update_comp_swap] at this
      · rintro ⟨v, hv⟩
        refine ⟨v, ?_⟩
        refine (ih (update σ (swapNat n) v)).mpr ?_
        rw [update_comp_swap]
        exact hv

theorem fv_term_swap : ∀ (t : Term) (x : Nat),
    (x ∈ fv_term (swapTerm t) ↔ swapNat x ∈ fv_term t) := by
  intro t
  induction t with
  | var v =>
      intro x
      simp [swapTerm, fv_term, swapNat_eq_iff]
  | zero => intro x; simp [swapTerm, fv_term]
  | succ t ih => intro x; simpa [swapTerm, fv_term] using ih x
  | add a b iha ihb => intro x; simp [swapTerm, fv_term, iha, ihb]
  | mul a b iha ihb => intro x; simp [swapTerm, fv_term, iha, ihb]
  | exp a b iha ihb => intro x; simp [swapTerm, fv_term, iha, ihb]

theorem fv_swap : ∀ (φ : Formula) (x : Nat),
    (x ∈ fv (swap01 φ) ↔ swapNat x ∈ fv φ) := by
  intro φ
  induction φ with
  | eq a b => intro x; simp [swap01, fv, fv_term_swap]
  | le a b => intro x; simp [swap01, fv, fv_term_swap]
  | not p ih => intro x; simpa [swap01, fv] using ih x
  | and p q ihp ihq => intro x; simp [swap01, fv, ihp, ihq]
  | or p q ihp ihq => intro x; simp [swap01, fv, ihp, ihq]
  | imp p q ihp ihq => intro x; simp [swap01, fv, ihp, ihq]
  | forall_ n p ih =>
      intro x
      simp only [swap01, fv, List.mem_filter, decide_eq_true_eq, ne_eq]
      rw [ih x]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun hc => h2 (by rw [← hc, swapNat_invol])⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun hc => h2 (by rw [hc, swapNat_invol])⟩
  | exists_ n p ih =>
      intro x
      simp only [swap01, fv, List.mem_filter, decide_eq_true_eq, ne_eq]
      rw [ih x]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun hc => h2 (by rw [← hc, swapNat_invol])⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun hc => h2 (by rw [hc, swapNat_invol])⟩
