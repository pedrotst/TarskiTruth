import Tarski.Wff
import Tarski.GodelEncoding

open Lang
open Godel

/-!
# Phase 1 — fuel monotonicity and determinism for `parseFormula`

Mirrors the `parseAtom_succ … parseAdd_succ` mutual block of `Tarski/Wff.lean`
for the five formula-level parsers.
-/

/-! ## Head-shape lemmas -/

theorem parseQuantifier_head :
    ∀ {fuel xs r}, parseFormula.parseQuantifier fuel xs = some r →
      (∃ ys, xs = L.all :: L.var :: ys) ∨ (∃ ys, xs = L.exi :: L.var :: ys) := by
  intro fuel xs r h
  cases fuel with
  | zero => simp [parseFormula.parseQuantifier] at h
  | succ fuel =>
    cases xs with
    | nil => simp [parseFormula.parseQuantifier] at h
    | cons a xs =>
      cases a
      case all =>
        cases xs with
        | nil => simp [parseFormula.parseQuantifier] at h
        | cons b xs =>
          cases b
          case var => exact Or.inl ⟨xs, rfl⟩
          all_goals simp [parseFormula.parseQuantifier] at h
      case exi =>
        cases xs with
        | nil => simp [parseFormula.parseQuantifier] at h
        | cons b xs =>
          cases b
          case var => exact Or.inr ⟨xs, rfl⟩
          all_goals simp [parseFormula.parseQuantifier] at h
      all_goals simp [parseFormula.parseQuantifier] at h

theorem parseAtom_none_head :
    ∀ (a : L), a ≠ L.O → a ≠ L.l_par → a ≠ L.var →
    ∀ (f : Nat) (t : L_formula), parseTerm.parseAtom f (a :: t) = none := by
  intro a hO hL hV f t
  cases f with
  | zero => simp [parseTerm.parseAtom]
  | succ f => cases a <;> simp_all [parseTerm.parseAtom]

theorem parseSucc_none_head :
    ∀ (a : L), a ≠ L.O → a ≠ L.l_par → a ≠ L.var →
    ∀ (f : Nat) (t : L_formula), parseTerm.parseSucc f (a :: t) = none := by
  intro a hO hL hV f t
  simp [parseTerm.parseSucc, parseAtom_none_head a hO hL hV]

theorem parseExp_none_head :
    ∀ (a : L), a ≠ L.O → a ≠ L.l_par → a ≠ L.var →
    ∀ (f : Nat) (t : L_formula), parseTerm.parseExp f (a :: t) = none := by
  intro a hO hL hV f t
  cases f with
  | zero => simp [parseTerm.parseExp]
  | succ f => simp [parseTerm.parseExp, parseSucc_none_head a hO hL hV]

theorem parseMul_none_head :
    ∀ (a : L), a ≠ L.O → a ≠ L.l_par → a ≠ L.var →
    ∀ (f : Nat) (t : L_formula), parseTerm.parseMul f (a :: t) = none := by
  intro a hO hL hV f t
  cases f with
  | zero => simp [parseTerm.parseMul]
  | succ f => simp [parseTerm.parseMul, parseExp_none_head a hO hL hV]

theorem parseAdd_none_head :
    ∀ (a : L), a ≠ L.O → a ≠ L.l_par → a ≠ L.var →
    ∀ (f : Nat) (t : L_formula), parseTerm.parseAdd f (a :: t) = none := by
  intro a hO hL hV f t
  cases f with
  | zero => simp [parseTerm.parseAdd]
  | succ f => simp [parseTerm.parseAdd, parseMul_none_head a hO hL hV]

theorem parseTerm_none_head :
    ∀ (a : L), a ≠ L.O → a ≠ L.l_par → a ≠ L.var →
    ∀ (f : Nat) (t : L_formula), parseTerm f (a :: t) = none := by
  intro a hO hL hV f t
  simp [parseTerm, parseAdd_none_head a hO hL hV]

theorem parseAtomic_none_head :
    ∀ (a : L), a ≠ L.O → a ≠ L.l_par → a ≠ L.var →
    ∀ (f : Nat) (t : L_formula), parseFormula.parseAtomic f (a :: t) = none := by
  intro a hO hL hV f t
  simp [parseFormula.parseAtomic, parseTerm_none_head a hO hL hV]

/-- `parseQuantifier` and `parseAtomic` never both succeed on the same input. -/
theorem parseAtomic_none_of_parseQuantifier {f₁ : Nat} {xs : L_formula}
    {r : Formula × L_formula} (f₂ : Nat)
    (h : parseFormula.parseQuantifier f₁ xs = some r) :
    parseFormula.parseAtomic f₂ xs = none := by
  rcases parseQuantifier_head h with ⟨ys, rfl⟩ | ⟨ys, rfl⟩
  · exact parseAtomic_none_head L.all (by simp) (by simp) (by simp) f₂ _
  · exact parseAtomic_none_head L.exi (by simp) (by simp) (by simp) f₂ _

/-! ## `parseAtomic` is monotone in fuel -/

theorem parseAtomic_succ :
    ∀ {fuel xs r},
      parseFormula.parseAtomic fuel xs = some r →
      parseFormula.parseAtomic (fuel + 1) xs = some r := by
  intro fuel xs r h
  cases hT : parseTerm fuel xs with
  | none => simp [parseFormula.parseAtomic, hT] at h
  | some p =>
    obtain ⟨t1, rest1⟩ := p
    have hT' : parseTerm (fuel + 1) xs = some (t1, rest1) := parseTerm_succ hT
    cases rest1 with
    | nil => simp [parseFormula.parseAtomic, hT] at h
    | cons a rest2 =>
      cases a
      case eq =>
        cases hT2 : parseTerm fuel rest2 with
        | none => simp [parseFormula.parseAtomic, hT, hT2] at h
        | some q =>
          obtain ⟨t2, rest3⟩ := q
          have hT2' : parseTerm (fuel + 1) rest2 = some (t2, rest3) := parseTerm_succ hT2
          simp [parseFormula.parseAtomic, hT, hT2] at h
          simp [parseFormula.parseAtomic, hT', hT2', ← h]
      case leq =>
        cases hT2 : parseTerm fuel rest2 with
        | none => simp [parseFormula.parseAtomic, hT, hT2] at h
        | some q =>
          obtain ⟨t2, rest3⟩ := q
          have hT2' : parseTerm (fuel + 1) rest2 = some (t2, rest3) := parseTerm_succ hT2
          simp [parseFormula.parseAtomic, hT, hT2] at h
          simp [parseFormula.parseAtomic, hT', hT2', ← h]
      all_goals simp [parseFormula.parseAtomic, hT] at h

/-! ## Unfolding the catch-all branches of `parseBase` and `parseNot` -/

theorem parseBase_fallback_some_q (fuel : Nat) (l : L_formula)
    (hl : ∀ ys, l ≠ L.l_par :: ys) {res : Formula × L_formula}
    (hQ : parseFormula.parseQuantifier fuel l = some res) :
    parseFormula.parseBase (fuel + 1) l = some res := by
  cases l with
  | nil => simp_all [parseFormula.parseBase]
  | cons a t => cases a <;> simp_all [parseFormula.parseBase]

theorem parseBase_fallback_some_a (fuel : Nat) (l : L_formula)
    (hl : ∀ ys, l ≠ L.l_par :: ys) {res : Formula × L_formula}
    (hQ : parseFormula.parseQuantifier fuel l = none)
    (hA : parseFormula.parseAtomic fuel l = some res) :
    parseFormula.parseBase (fuel + 1) l = some res := by
  cases l with
  | nil => simp_all [parseFormula.parseBase]
  | cons a t => cases a <;> simp_all [parseFormula.parseBase]

theorem parseBase_fallback_none (fuel : Nat) (l : L_formula)
    (hl : ∀ ys, l ≠ L.l_par :: ys)
    (hQ : parseFormula.parseQuantifier fuel l = none)
    (hA : parseFormula.parseAtomic fuel l = none) :
    parseFormula.parseBase (fuel + 1) l = none := by
  cases l with
  | nil => simp only [parseFormula.parseBase, hQ, hA]
  | cons a t =>
    cases a <;>
      first
      | exact absurd rfl (hl t)
      | simp only [parseFormula.parseBase, hQ, hA]

theorem parseNot_fallback_eq (fuel : Nat) (l : L_formula)
    (hl : ∀ ys, l ≠ L.not :: L.l_par :: ys) :
    parseFormula.parseNot (fuel + 1) l = parseFormula.parseBase fuel l := by
  cases l with
  | nil => simp [parseFormula.parseNot]
  | cons a t =>
    cases a
    case not =>
      cases t with
      | nil => simp [parseFormula.parseNot]
      | cons b t2 =>
        cases b
        case l_par => exact absurd rfl (hl t2)
        all_goals simp [parseFormula.parseNot]
    all_goals simp [parseFormula.parseNot]

/-! ## The mutual monotonicity block -/

mutual

theorem parseQuantifier_succ :
    ∀ {fuel xs r},
      parseFormula.parseQuantifier fuel xs = some r →
      parseFormula.parseQuantifier (fuel + 1) xs = some r := by
  intro fuel xs r h
  cases fuel with
  | zero => simp [parseFormula.parseQuantifier] at h
  | succ fuel =>
    cases xs with
    | nil => simp [parseFormula.parseQuantifier] at h
    | cons a xs =>
      cases a
      case all =>
        cases xs with
        | nil => simp [parseFormula.parseQuantifier] at h
        | cons b xs =>
          cases b
          case var =>
            cases hC : countPrimes xs with
            | mk n rest1 =>
              cases rest1 with
              | nil => simp [parseFormula.parseQuantifier, hC] at h
              | cons c rest2 =>
                cases c
                case l_par =>
                  cases hI : parseFormula.parseNot fuel rest2 with
                  | none => simp [parseFormula.parseQuantifier, hC, hI] at h
                  | some p =>
                    have hI' : parseFormula.parseNot (fuel + 1) rest2 = some p :=
                      parseNot_succ hI
                    have hg : parseFormula.parseQuantifier (fuel + 1 + 1) (L.all :: L.var :: xs)
                        = parseFormula.parseQuantifier (fuel + 1) (L.all :: L.var :: xs) := by
                      simp [parseFormula.parseQuantifier, hC, hI, hI']
                    rw [hg]; exact h
                all_goals simp [parseFormula.parseQuantifier, hC] at h
          all_goals simp [parseFormula.parseQuantifier] at h
      case exi =>
        cases xs with
        | nil => simp [parseFormula.parseQuantifier] at h
        | cons b xs =>
          cases b
          case var =>
            cases hC : countPrimes xs with
            | mk n rest1 =>
              cases rest1 with
              | nil => simp [parseFormula.parseQuantifier, hC] at h
              | cons c rest2 =>
                cases c
                case l_par =>
                  cases hI : parseFormula.parseNot fuel rest2 with
                  | none => simp [parseFormula.parseQuantifier, hC, hI] at h
                  | some p =>
                    have hI' : parseFormula.parseNot (fuel + 1) rest2 = some p :=
                      parseNot_succ hI
                    have hg : parseFormula.parseQuantifier (fuel + 1 + 1) (L.exi :: L.var :: xs)
                        = parseFormula.parseQuantifier (fuel + 1) (L.exi :: L.var :: xs) := by
                      simp [parseFormula.parseQuantifier, hC, hI, hI']
                    rw [hg]; exact h
                all_goals simp [parseFormula.parseQuantifier, hC] at h
          all_goals simp [parseFormula.parseQuantifier] at h
      all_goals simp [parseFormula.parseQuantifier] at h
termination_by fuel _ _ => fuel
decreasing_by all_goals omega

theorem parseBase_succ :
    ∀ {fuel xs r},
      parseFormula.parseBase fuel xs = some r →
      parseFormula.parseBase (fuel + 1) xs = some r := by
  intro fuel xs r h
  cases fuel with
  | zero => simp [parseFormula.parseBase] at h
  | succ fuel =>
    by_cases hlp : ∃ ys, xs = L.l_par :: ys
    · obtain ⟨ys, rfl⟩ := hlp
      cases hI : parseFormula.parseNot fuel ys with
      | none => simp [parseFormula.parseBase, hI] at h
      | some p =>
        have hI' : parseFormula.parseNot (fuel + 1) ys = some p := parseNot_succ hI
        obtain ⟨p1, rest1⟩ := p
        cases rest1 with
        | nil =>
          have hg : parseFormula.parseBase (fuel + 1 + 1) (L.l_par :: ys)
              = parseFormula.parseBase (fuel + 1) (L.l_par :: ys) := by
            simp [parseFormula.parseBase, hI, hI']
          rw [hg]; exact h
        | cons b rest2 =>
          cases b <;>
            first
            | (have hg : parseFormula.parseBase (fuel + 1 + 1) (L.l_par :: ys)
                   = parseFormula.parseBase (fuel + 1) (L.l_par :: ys) := by
                 simp [parseFormula.parseBase, hI, hI']
               rw [hg]; exact h)
            | (cases hJ : parseFormula.parseNot fuel rest2 with
               | none => simp [parseFormula.parseBase, hI, hJ] at h
               | some q =>
                 have hJ' : parseFormula.parseNot (fuel + 1) rest2 = some q :=
                   parseNot_succ hJ
                 have hg : parseFormula.parseBase (fuel + 1 + 1) (L.l_par :: ys)
                     = parseFormula.parseBase (fuel + 1) (L.l_par :: ys) := by
                   simp [parseFormula.parseBase, hI, hI', hJ, hJ']
                 rw [hg]; exact h)
    · have hl : ∀ ys, xs ≠ L.l_par :: ys := fun ys hy => hlp ⟨ys, hy⟩
      cases hQ : parseFormula.parseQuantifier fuel xs with
      | some res =>
        have hQ' : parseFormula.parseQuantifier (fuel + 1) xs = some res :=
          parseQuantifier_succ hQ
        rw [parseBase_fallback_some_q fuel xs hl hQ] at h
        rw [parseBase_fallback_some_q (fuel + 1) xs hl hQ']
        exact h
      | none =>
        cases hA : parseFormula.parseAtomic fuel xs with
        | none =>
          rw [parseBase_fallback_none fuel xs hl hQ hA] at h
          exact absurd h (by simp)
        | some res =>
          have hA' : parseFormula.parseAtomic (fuel + 1) xs = some res := parseAtomic_succ hA
          have hQ2 : parseFormula.parseQuantifier (fuel + 1) xs = none := by
            cases hQ2' : parseFormula.parseQuantifier (fuel + 1) xs with
            | none => rfl
            | some r2 =>
              rw [parseAtomic_none_of_parseQuantifier fuel hQ2'] at hA
              exact absurd hA (by simp)
          rw [parseBase_fallback_some_a fuel xs hl hQ hA] at h
          rw [parseBase_fallback_some_a (fuel + 1) xs hl hQ2 hA']
          exact h
termination_by fuel _ _ => fuel
decreasing_by all_goals omega

theorem parseNot_succ :
    ∀ {fuel xs r},
      parseFormula.parseNot fuel xs = some r →
      parseFormula.parseNot (fuel + 1) xs = some r := by
  intro fuel xs r h
  cases fuel with
  | zero => simp [parseFormula.parseNot] at h
  | succ fuel =>
    by_cases hnl : ∃ ys, xs = L.not :: L.l_par :: ys
    · obtain ⟨ys, rfl⟩ := hnl
      cases hI : parseFormula.parseNot fuel ys with
      | none => simp [parseFormula.parseNot, hI] at h
      | some p =>
        have hI' : parseFormula.parseNot (fuel + 1) ys = some p := parseNot_succ hI
        have hg : parseFormula.parseNot (fuel + 1 + 1) (L.not :: L.l_par :: ys)
            = parseFormula.parseNot (fuel + 1) (L.not :: L.l_par :: ys) := by
          simp [parseFormula.parseNot, hI, hI']
        rw [hg]; exact h
    · have hl : ∀ ys, xs ≠ L.not :: L.l_par :: ys := fun ys hy => hnl ⟨ys, hy⟩
      rw [parseNot_fallback_eq fuel xs hl] at h
      rw [parseNot_fallback_eq (fuel + 1) xs hl]
      exact parseBase_succ h
termination_by fuel _ _ => fuel
decreasing_by all_goals omega

end

/-! ## Top level -/

theorem parseImp_succ :
    ∀ {fuel xs r},
      parseFormula.parseImp fuel xs = some r →
      parseFormula.parseImp (fuel + 1) xs = some r := by
  intro fuel xs r h
  have h' : parseFormula.parseNot fuel xs = some r := by
    simpa [parseFormula.parseImp] using h
  simpa [parseFormula.parseImp] using parseNot_succ h'

theorem parseFormula_succ :
    ∀ {fuel xs r},
      parseFormula fuel xs = some r →
      parseFormula (fuel + 1) xs = some r := by
  intro fuel xs r h
  simpa [parseFormula] using parseImp_succ (by simpa [parseFormula] using h)

theorem parseFormula_mono
    {fuel₁ fuel₂ : Nat} {xs : L_formula} {r : Formula × L_formula}
    (h₁₂ : fuel₁ ≤ fuel₂)
    (h : parseFormula fuel₁ xs = some r) :
    parseFormula fuel₂ xs = some r := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h₁₂
  induction d generalizing fuel₁ with
  | zero => simpa using h
  | succ d ih =>
      have h2 : fuel₁ ≤ fuel₁ + d := by omega
      have h' : parseFormula (fuel₁ + d) xs = some r := ih h h2
      simpa [Nat.add_assoc] using (parseFormula_succ h')

theorem parse_det_le
    {fuel₁ fuel₂ : Nat} {xs : L_formula} {φ₁ φ₂ : Formula}
    (hle : fuel₁ ≤ fuel₂)
    (h1 : parse fuel₁ xs = some φ₁)
    (h2 : parse fuel₂ xs = some φ₂) :
    φ₁ = φ₂ := by
  cases hp : parseFormula fuel₁ xs with
  | none =>
    simp only [parse, hp] at h1
    simp at h1
  | some p =>
    obtain ⟨φ, rest⟩ := p
    have hp' : parseFormula fuel₂ xs = some (φ, rest) := parseFormula_mono hle hp
    cases rest with
    | nil =>
      simp only [parse, hp] at h1
      simp only [parse, hp'] at h2
      simp at h1 h2
      rw [← h1, ← h2]
    | cons a t =>
      simp only [parse, hp] at h1
      simp at h1

theorem parse_det
    {fuel₁ fuel₂ : Nat} {xs : L_formula} {φ₁ φ₂ : Formula}
    (h1 : parse fuel₁ xs = some φ₁)
    (h2 : parse fuel₂ xs = some φ₂) :
    φ₁ = φ₂ := by
  cases Nat.le_total fuel₁ fuel₂ with
  | inl hle => exact parse_det_le hle h1 h2
  | inr hle => exact (parse_det_le hle h2 h1).symm

theorem decode_det
    {fuel₁ fuel₂ n : Nat} {φ₁ φ₂ : Formula}
    (h1 : decode fuel₁ n = some φ₁)
    (h2 : decode fuel₂ n = some φ₂) :
    φ₁ = φ₂ := by
  cases hd : decodeL n with
  | none =>
    simp only [decode, hd] at h1
    simp at h1
  | some xs =>
    cases hp1 : parse fuel₁ xs with
    | none =>
      simp only [decode, hd, hp1] at h1
      simp at h1
    | some ψ₁ =>
      cases hp2 : parse fuel₂ xs with
      | none =>
        simp only [decode, hd, hp2] at h2
        simp at h2
      | some ψ₂ =>
        simp only [decode, hd, hp1] at h1
        simp only [decode, hd, hp2] at h2
        simp at h1 h2
        rw [← h1, ← h2]
        exact parse_det hp1 hp2
