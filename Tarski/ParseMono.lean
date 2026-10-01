import Tarski.Wff
import Tarski.GodelEncoding

open Lang
open Godel

/-!
# Phase 1 — fuel monotonicity and determinism for `parseFormula`

Mirrors the `parseAtom_succ … parseAdd_succ` mutual block of `Tarski/Wff.lean`
for the five formula-level parsers.

Since the grammar fix (atomic formulas are prefix-marked by `=` / `≤`), every
branch of `parseFormula.parseBase` is selected by the head symbol alone, so the
monotonicity proofs need no disjointness reasoning: each recursive call simply
drops the fuel by one.
-/

theorem parseAtomic_succ :
    ∀ {fuel xs r},
      parseFormula.parseAtomic fuel xs = some r →
      parseFormula.parseAtomic (fuel + 1) xs = some r := by
  intro fuel xs r h
  cases xs with
  | nil => simp at h
  | cons a ys =>
    cases a
    case eq =>
      cases h1 : parseTerm fuel ys with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨t1, rest1⟩ := p1
        cases h2 : parseTerm fuel rest1 with
        | none => simp [h1, h2] at h
        | some p2 =>
          obtain ⟨t2, rest2⟩ := p2
          have e : parseFormula.parseAtomic (fuel + 1) (L.eq :: ys)
                 = parseFormula.parseAtomic fuel (L.eq :: ys) := by
            simp [h1, h2, parseTerm_succ h1, parseTerm_succ h2]
          rw [e]; exact h
    case leq =>
      cases h1 : parseTerm fuel ys with
      | none => simp [h1] at h
      | some p1 =>
        obtain ⟨t1, rest1⟩ := p1
        cases h2 : parseTerm fuel rest1 with
        | none => simp [h1, h2] at h
        | some p2 =>
          obtain ⟨t2, rest2⟩ := p2
          have e : parseFormula.parseAtomic (fuel + 1) (L.leq :: ys)
                 = parseFormula.parseAtomic fuel (L.leq :: ys) := by
            simp [h1, h2, parseTerm_succ h1, parseTerm_succ h2]
          rw [e]; exact h
    all_goals simp at h

mutual

theorem parseQuantifier_succ :
    ∀ {fuel xs r},
      parseFormula.parseQuantifier fuel xs = some r →
      parseFormula.parseQuantifier (fuel + 1) xs = some r := by
  intro fuel xs r h
  cases fuel with
  | zero => simp at h
  | succ fuel =>
    cases xs with
    | nil => simp at h
    | cons a ys =>
      cases a
      case all =>
        cases ys with
        | nil => simp at h
        | cons b zs =>
          cases b
          case var =>
            cases hc : countPrimes zs with
            | mk n rest1 =>
              cases rest1 with
              | nil => simp [hc] at h
              | cons c rest2 =>
                cases c
                case l_par =>
                  cases hp : parseFormula.parseNot fuel rest2 with
                  | none => simp [hc, hp] at h
                  | some pr =>
                    obtain ⟨p, rest3⟩ := pr
                    cases rest3 with
                    | nil => simp [hc, hp] at h
                    | cons d rest4 =>
                      cases d
                      case r_par =>
                        simp [hc, hp] at h
                        simp [hc, parseNot_succ hp, ← h]
                      all_goals simp [hc, hp] at h
                all_goals simp [hc] at h
          all_goals simp at h
      case exi =>
        cases ys with
        | nil => simp at h
        | cons b zs =>
          cases b
          case var =>
            cases hc : countPrimes zs with
            | mk n rest1 =>
              cases rest1 with
              | nil => simp [hc] at h
              | cons c rest2 =>
                cases c
                case l_par =>
                  cases hp : parseFormula.parseNot fuel rest2 with
                  | none => simp [hc, hp] at h
                  | some pr =>
                    obtain ⟨p, rest3⟩ := pr
                    cases rest3 with
                    | nil => simp [hc, hp] at h
                    | cons d rest4 =>
                      cases d
                      case r_par =>
                        simp [hc, hp] at h
                        simp [hc, parseNot_succ hp, ← h]
                      all_goals simp [hc, hp] at h
                all_goals simp [hc] at h
          all_goals simp at h
      all_goals simp at h
termination_by fuel _ _ => fuel

theorem parseNot_succ :
    ∀ {fuel xs r},
      parseFormula.parseNot fuel xs = some r →
      parseFormula.parseNot (fuel + 1) xs = some r := by
  intro fuel xs r h
  cases fuel with
  | zero => simp at h
  | succ fuel =>
    cases xs with
    | nil =>
        simp only [parseFormula.parseNot] at h ⊢
        exact parseBase_succ h
    | cons a ys =>
      cases a
      case not =>
        cases ys with
        | nil =>
            simp only [parseFormula.parseNot] at h ⊢
            exact parseBase_succ h
        | cons b zs =>
          cases b
          case l_par =>
            cases hp : parseFormula.parseNot fuel zs with
            | none => simp [hp] at h
            | some pr =>
              obtain ⟨p, rest1⟩ := pr
              cases rest1 with
              | nil => simp [hp] at h
              | cons c rest2 =>
                cases c
                case r_par =>
                  simp [hp] at h
                  simp [parseNot_succ hp, ← h]
                all_goals simp [hp] at h
          all_goals
            simp only [parseFormula.parseNot] at h ⊢
            exact parseBase_succ h
      all_goals
        simp only [parseFormula.parseNot] at h ⊢
        exact parseBase_succ h
termination_by fuel _ _ => fuel

theorem parseBase_succ :
    ∀ {fuel xs r},
      parseFormula.parseBase fuel xs = some r →
      parseFormula.parseBase (fuel + 1) xs = some r := by
  intro fuel xs r h
  cases fuel with
  | zero => simp at h
  | succ fuel =>
    cases xs with
    | nil => simp at h
    | cons a ys =>
      cases a
      case l_par =>
        cases hp : parseFormula.parseNot fuel ys with
        | none => simp [hp] at h
        | some pr =>
          obtain ⟨p, rest1⟩ := pr
          have hp' := parseNot_succ hp
          cases rest1 with
          | nil => simp [hp] at h
          | cons c rest2 =>
            cases c
            case r_par =>
              simp [hp] at h
              simp [hp', ← h]
            case and =>
              cases hq : parseFormula.parseNot fuel rest2 with
              | none => simp [hp, hq] at h
              | some qr =>
                obtain ⟨q, rest3⟩ := qr
                have hq' := parseNot_succ hq
                cases rest3 with
                | nil => simp [hp, hq] at h
                | cons d rest4 =>
                  cases d
                  case r_par =>
                    simp [hp, hq] at h
                    simp [hp', hq', ← h]
                  all_goals simp [hp, hq] at h
            case or =>
              cases hq : parseFormula.parseNot fuel rest2 with
              | none => simp [hp, hq] at h
              | some qr =>
                obtain ⟨q, rest3⟩ := qr
                have hq' := parseNot_succ hq
                cases rest3 with
                | nil => simp [hp, hq] at h
                | cons d rest4 =>
                  cases d
                  case r_par =>
                    simp [hp, hq] at h
                    simp [hp', hq', ← h]
                  all_goals simp [hp, hq] at h
            case imp =>
              cases hq : parseFormula.parseNot fuel rest2 with
              | none => simp [hp, hq] at h
              | some qr =>
                obtain ⟨q, rest3⟩ := qr
                have hq' := parseNot_succ hq
                cases rest3 with
                | nil => simp [hp, hq] at h
                | cons d rest4 =>
                  cases d
                  case r_par =>
                    simp [hp, hq] at h
                    simp [hp', hq', ← h]
                  all_goals simp [hp, hq] at h
            all_goals simp [hp] at h
      case all =>
        simp only [parseFormula.parseBase] at h ⊢
        exact parseQuantifier_succ h
      case exi =>
        simp only [parseFormula.parseBase] at h ⊢
        exact parseQuantifier_succ h
      case eq =>
        simp only [parseFormula.parseBase] at h ⊢
        exact parseAtomic_succ h
      case leq =>
        simp only [parseFormula.parseBase] at h ⊢
        exact parseAtomic_succ h
      all_goals simp at h
termination_by fuel _ _ => fuel

end

theorem parseFormula_succ :
    ∀ {fuel xs r},
      parseFormula fuel xs = some r →
      parseFormula (fuel + 1) xs = some r := by
  intro fuel xs r h
  simp only [parseFormula, parseFormula.parseImp] at h ⊢
  exact parseNot_succ h

theorem parseFormula_mono
    {fuel₁ fuel₂ : Nat} {xs : L_formula} {r : Formula × L_formula}
    (h₁₂ : fuel₁ ≤ fuel₂)
    (h : parseFormula fuel₁ xs = some r) :
    parseFormula fuel₂ xs = some r := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h₁₂
  induction d generalizing fuel₁ with
  | zero =>
      simpa using h
  | succ d ih =>
      have h2 : fuel₁ ≤ fuel₁ + d := by omega
      have h' : parseFormula (fuel₁ + d) xs = some r := ih h h2
      simpa [Nat.add_assoc] using (parseFormula_succ h')

theorem parse_det
    {fuel₁ fuel₂ : Nat} {xs : L_formula} {φ₁ φ₂ : Formula}
    (h1 : parse fuel₁ xs = some φ₁)
    (h2 : parse fuel₂ xs = some φ₂) :
    φ₁ = φ₂ := by
  cases hp1 : parseFormula fuel₁ xs with
  | none =>
      simp only [parse, hp1, Option.bind_eq_bind, Option.bind_none] at h1
      exact absurd h1 (by simp)
  | some r1 =>
    cases hp2 : parseFormula fuel₂ xs with
    | none =>
        simp only [parse, hp2, Option.bind_eq_bind, Option.bind_none] at h2
        exact absurd h2 (by simp)
    | some r2 =>
      have hsame : r1 = r2 := by
        cases Nat.le_total fuel₁ fuel₂ with
        | inl hle =>
            have hm := parseFormula_mono hle hp1
            rw [hp2] at hm
            injection hm with hm
            exact hm.symm
        | inr hle =>
            have hm := parseFormula_mono hle hp2
            rw [hp1] at hm
            injection hm with hm
      subst hsame
      simp only [parse, hp1] at h1
      simp only [parse, hp2] at h2
      rw [h1] at h2
      injection h2 with h2

theorem decode_det
    {fuel₁ fuel₂ n : Nat} {φ₁ φ₂ : Formula}
    (h1 : decode fuel₁ n = some φ₁)
    (h2 : decode fuel₂ n = some φ₂) :
    φ₁ = φ₂ := by
  cases hd : decodeL n with
  | none => 
      simp only [decode, hd] at h1
      exact absurd h1 (by simp)
  | some xs =>
    simp only [decode, hd] at h1 h2
    cases hp1 : parse fuel₁ xs with
    | none => 
        simp only [hp1] at h1
        exact absurd h1 (by simp)
    | some ψ₁ =>
      cases hp2 : parse fuel₂ xs with
      | none => 
          simp only [hp2] at h2
          exact absurd h2 (by simp)
      | some ψ₂ =>
        simp only [hp1] at h1
        simp only [hp2] at h2
        injection h1 with h1
        injection h2 with h2
        rw [← h1, ← h2]
        exact parse_det hp1 hp2
