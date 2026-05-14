namespace Env

abbrev Assignment := Nat → Nat

@[simp]
def empty_ctx : Assignment := fun _ => 0

@[simp]
def update (σ : Assignment) (x : Nat) (v : Nat) : Assignment :=
  fun y => if y = x then v else σ y

@[simp]
theorem env_neq :
  t ≠ x →
  (update σ x v) t = σ t := by
  intro h
  simp [update, h]

@[simp]
theorem env_shadow :
  update (update σ x v1) x v2 = update σ x v2 := by
  funext y
  have h : y = x ∨ y ≠ x := by grind
  cases h with
  | inl h => simp [update, h]
  | inr h =>
    repeat rw [env_neq h]

theorem env_comm :
  x ≠ y →
  update (update σ x v1) y v2 = update (update σ y v2) x v1 := by
  intro h
  funext n
  by_cases x_eq_n : n = x
  · by_cases y_eq_n : n = y
    · subst x_eq_n
      contradiction
    · subst x_eq_n
      simp
      intro
      contradiction
  · by_cases y_eq_n : n = y
    · subst y_eq_n
      simp
      intro
      contradiction
    · simp [y_eq_n]
-- theorem env_same :
--   update σ x (σ y) = update σ x y := by
--   funext z
--   have h : z = x ∨ z ≠ x := by grind
--   cases h with
--   | inl h =>
--     rw [update, h]
--     simp [update]
--   |inr h =>
--     rw [update, env_neq h, h]






end Env
