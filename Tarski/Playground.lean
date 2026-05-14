inductive Tok where
  | lpar
  | rpar
  | v
  | plus
  | times
deriving Repr, DecidableEq

inductive Term where
  | var
  | add (t₁ t₂ : Term)
  | mul (t₁ t₂ : Term)
deriving Repr, DecidableEq

open Tok
open Term

def parseTerm (fuel : Nat) (xs : List Tok) : Option (Term × List Tok) :=
  parseAdd fuel xs
where
  parseAtom : Nat → List Tok → Option (Term × List Tok)
    | 0, _ => none
    | _, v :: xs =>
        some (.var, xs)
    | fuel + 1, lpar :: xs => do
        let (t, rest) ← parseAdd fuel xs
        match rest with
        | rpar :: ys => some (t, ys)
        | _ => none
    | _, _ =>
        none

  parseMulLoop : Nat → Term → List Tok → Option (Term × List Tok)
    | 0, _, times :: _ => none
    | 0, acc, ys => some (acc, ys)
    | fuel + 1, acc, times :: ys => do
        let (rhs, zs) ← parseAtom (fuel + 1) ys
        parseMulLoop fuel (.mul acc rhs) zs
    | _, acc, ys =>
        some (acc, ys)

  parseMul : Nat → List Tok → Option (Term × List Tok)
    | 0, _ => none
    | fuel + 1, xs => do
        let (lhs, rest) ← parseAtom (fuel + 1) xs
        parseMulLoop fuel lhs rest

  parseAddLoop : Nat → Term → List Tok → Option (Term × List Tok)
    | 0, _, plus :: _ => none
    | 0, acc, ys => some (acc, ys)
    | fuel + 1, acc, plus :: ys => do
        let (rhs, zs) ← parseMul (fuel + 1) ys
        parseAddLoop fuel (.add acc rhs) zs
    | _, acc, ys =>
        some (acc, ys)

  parseAdd : Nat → List Tok → Option (Term × List Tok)
    | 0, _ => none
    | fuel + 1, xs => do
        let (lhs, rest) ← parseMul (fuel + 1) xs
        parseAddLoop fuel lhs rest

def parse (xs : List Tok) : Option Term := do
  let (t, rest) ← parseTerm xs.length xs
  match rest with
  | [] => some t
  | _  => none

#eval parse [v]
-- some Term.var

#eval parse [v, plus, v, times, v]
-- some (Term.add Term.var (Term.mul Term.var Term.var))

#eval parse [lpar, v, plus, v, rpar, times, v]
-- some (Term.mul (Term.add Term.var Term.var) Term.var)

mutual
theorem parseAtom_succ :
    ∀ {fuel xs r},
      parseTerm.parseAtom fuel xs = some r →
      parseTerm.parseAtom (fuel + 1) xs = some r := by
  intro fuel xs r h
  cases fuel with
  | zero =>
    cases xs <;> simp [parseTerm.parseAtom] at h
  | succ fuel =>
    cases xs with
    | nil =>
      simp [parseTerm.parseAtom] at h
    | cons a xs =>
      cases a <;> try (simp [parseTerm.parseAtom])
      case lpar =>
        cases hAdd : parseTerm.parseAdd fuel xs <;> simp [parseTerm.parseAtom, hAdd] at h
        rename_i p
        obtain ⟨t, rest⟩ := p
        cases rest with
        | nil =>
          simp at h
        | cons b ys =>
          cases b <;> try (simp at h)
          case rpar =>
            cases h
            have hAdd' :
              parseTerm.parseAdd (fuel + 1) xs = some (t, Tok.rpar :: ys) :=
              parseAdd_succ hAdd
            simp [hAdd']
      case rpar =>
        simp [parseTerm.parseAtom] at h
      case v =>
       simp [parseTerm.parseAtom] at h
       grind
      case plus =>
       simp [parseTerm.parseAtom] at h
      case times =>
       simp [parseTerm.parseAtom] at h
termination_by fuel _ _ => (fuel, 0)
decreasing_by
  subst_vars
  simp_wf
  omega

theorem parseMul_succ :
    ∀ {fuel xs r},
      parseTerm.parseMul fuel xs = some r →
      parseTerm.parseMul (fuel + 1) xs = some r := by
  intro fuel xs r h
  cases fuel with
  | zero =>
    -- cases fuel <;> simp [parseTerm.parseMulLoop] at * <;> grind
      simp [parseTerm.parseMul] at h
  | succ fuel =>
      cases hA : parseTerm.parseAtom (fuel + 1) xs with
      | none =>
          simp [parseTerm.parseMul, hA] at h
      | some p =>
          cases p with
          | mk lhs rest =>
              have hLoop :
                  parseTerm.parseMulLoop fuel lhs rest = some r := by
                simpa [parseTerm.parseMul, hA] using h
              have hA' :
                  parseTerm.parseAtom (fuel + 2) xs = some (lhs, rest) :=
                parseAtom_succ hA
              have hLoop' :
                  parseTerm.parseMulLoop (fuel + 1) lhs rest = some r :=
                parseMulLoop_succ hLoop
              simpa [parseTerm.parseMul, hA'] using hLoop'

termination_by fuel _ _ => (fuel, 1)
decreasing_by
  subst_vars
  · refine Prod.Lex.right ?_ ?_
    omega
  · subst_vars
    apply Prod.Lex.left
    omega

theorem parseAdd_succ :
    ∀ {fuel xs r},
      parseTerm.parseAdd fuel xs = some r →
      parseTerm.parseAdd (fuel + 1) xs = some r := by
  intro fuel xs r h
  cases fuel with
  | zero =>
      simp [parseTerm.parseAdd] at h
  | succ fuel =>
      cases hM : parseTerm.parseMul (fuel + 1) xs with
      | none =>
          simp [parseTerm.parseAdd, hM] at h
      | some p =>
          cases p with
          | mk lhs rest =>
              have hLoop :
                  parseTerm.parseAddLoop fuel lhs rest = some r := by
                simpa [parseTerm.parseAdd, hM] using h
              have hM' :
                  parseTerm.parseMul (fuel + 2) xs = some (lhs, rest) :=
                parseMul_succ hM
              have hLoop' :
                  parseTerm.parseAddLoop (fuel + 1) lhs rest = some r :=
                parseAddLoop_succ hLoop
              simpa [parseTerm.parseAdd, hM'] using hLoop'
termination_by fuel _ _ => (fuel, 2)
decreasing_by
  subst_vars
  · refine Prod.Lex.right ?_ ?_
    omega
  · subst_vars
    apply Prod.Lex.left
    omega


theorem parseAddLoop_succ :
    ∀ {fuel acc xs r},
      parseTerm.parseAddLoop fuel acc xs = some r →
      parseTerm.parseAddLoop (fuel + 1) acc xs = some r := by
  intro fuel acc xs r h
  cases xs with
  | nil =>
    cases fuel <;> simp [parseTerm.parseAddLoop] at * <;> grind
  | cons a xs =>
      cases a <;> try (simpa [parseTerm.parseAddLoop] using h)
      case plus =>
        cases fuel with
        | zero =>
            simp [parseTerm.parseAddLoop] at h
        | succ fuel =>
            cases hM : parseTerm.parseMul (fuel + 1) xs with
            | none =>
                simp [parseTerm.parseAddLoop, hM] at h
            | some p =>
                cases p with
                | mk rhs zs =>
                    have hLoop :
                        parseTerm.parseAddLoop fuel (.add acc rhs) zs = some r := by
                      simpa [parseTerm.parseAddLoop, hM] using h
                    have hM' :
                        parseTerm.parseMul (fuel + 2) xs = some (rhs, zs) :=
                      parseMul_succ hM
                    have hLoop' :
                        parseTerm.parseAddLoop (fuel + 1) (.add acc rhs) zs = some r :=
                      parseAddLoop_succ hLoop
                    simpa [parseTerm.parseAddLoop, hM'] using hLoop'
      case lpar =>
        cases fuel <;> simp [parseTerm.parseAddLoop] at * <;> assumption
      case rpar =>
        cases fuel <;> simp [parseTerm.parseAddLoop] at * <;> assumption
      case v =>
        cases fuel <;> simp [parseTerm.parseAddLoop] at * <;> assumption
      case times =>
        cases fuel <;> simp [parseTerm.parseAddLoop] at * <;> assumption
termination_by fuel _ _ => (fuel, 4)
decreasing_by
  subst_vars
  · refine Prod.Lex.right ?_ ?_
    omega
  · subst_vars
    apply Prod.Lex.left
    omega


theorem parseMulLoop_succ :
    ∀ {fuel acc xs r},
      parseTerm.parseMulLoop fuel acc xs = some r →
      parseTerm.parseMulLoop (fuel + 1) acc xs = some r := by
  intro fuel acc xs r h
  cases xs with
  | nil =>
    cases fuel <;> simp [parseTerm.parseMulLoop] at * <;> grind
  | cons a xs =>
      cases a <;> try (simpa [parseTerm.parseMulLoop] using h)
      case times =>
        cases fuel with
        | zero =>
            simp [parseTerm.parseMulLoop] at h
        | succ fuel =>
            cases hA : parseTerm.parseAtom (fuel + 1) xs with
            | none =>
                simp [parseTerm.parseMulLoop, hA] at h
            | some p =>
                cases p with
                | mk rhs zs =>
                    have hLoop :
                        parseTerm.parseMulLoop fuel (.mul acc rhs) zs = some r := by
                      simpa [parseTerm.parseMulLoop, hA] using h
                    have hA' :
                        parseTerm.parseAtom (fuel + 2) xs = some (rhs, zs) :=
                      parseAtom_succ hA
                    have hLoop' :
                        parseTerm.parseMulLoop (fuel + 1) (.mul acc rhs) zs = some r :=
                      parseMulLoop_succ hLoop
                    simpa [parseTerm.parseMulLoop, hA'] using hLoop'
      case lpar =>
        cases fuel <;> simp [parseTerm.parseMulLoop] at * <;> assumption
      case rpar =>
        cases fuel <;> simp [parseTerm.parseMulLoop] at * <;> assumption
      case v =>
        cases fuel <;> simp [parseTerm.parseMulLoop] at * <;> assumption
      case plus =>
        cases fuel <;> simp [parseTerm.parseMulLoop] at * <;> assumption
termination_by fuel _ _ => (fuel, 3)
decreasing_by
  subst_vars
  · refine Prod.Lex.right ?_ ?_
    omega
  · subst_vars
    apply Prod.Lex.left
    omega

end

theorem parseTerm_succ :
    ∀ {fuel xs r},
      parseTerm fuel xs = some r →
      parseTerm (fuel + 1) xs = some r := by
  intro fuel xs r h
  simpa [parseTerm] using (parseAdd_succ h)


theorem parseTerm_mono
    {fuel₁ fuel₂ : Nat} {xs : List Tok} {r : Term × List Tok}
    (h₁₂ : fuel₁ ≤ fuel₂)
    (h : parseTerm fuel₁ xs = some r) :
    parseTerm fuel₂ xs = some r := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h₁₂
  induction d generalizing fuel₁ with
  | zero =>
    simpa using h
  | succ d ih =>
    have h2 : fuel₁ ≤ fuel₁ + d := by grind
    have h' : parseTerm (fuel₁ + d) xs = some r := ih h h2
    simpa [Nat.add_assoc] using (parseTerm_succ h')

theorem parseTerm_det_sameFuel
    {fuel : Nat} {xs : List Tok} {r₁ r₂ : Term × List Tok}
    (h1 : parseTerm fuel xs = some r₁)
    (h2 : parseTerm fuel xs = some r₂) :
    r₁ = r₂ := by
  simpa [h1] using h2

theorem parseTerm_det_diff_fuel
    {fuel₁ fuel₂ : Nat} {xs : List Tok} {r₁ r₂ : Term × List Tok}
    (h1 : parseTerm fuel₁ xs = some r₁)
    (h2 : parseTerm fuel₂ xs = some r₂) :
    r₁ = r₂ := by
  cases Nat.le_total fuel₁ fuel₂ with
  | inl h₁₂ =>
      have h1' : parseTerm fuel₂ xs = some r₁ := parseTerm_mono h₁₂ h1
      exact parseTerm_det_sameFuel h1' h2
  | inr h₂₁ =>
      have h2' : parseTerm fuel₁ xs = some r₂ := parseTerm_mono h₂₁ h2
      exact parseTerm_det_sameFuel h1 h2'
