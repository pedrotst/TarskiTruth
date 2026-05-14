import Tarski.Lang

open Lang

def wff_var (l : L_formula) : Prop :=
  ∃ n, l = (L.var :: List.replicate n L.prime)

inductive wff_num : L_formula → Prop where
| wff_O : wff_num [L.O]
| wff_S : forall l : L_formula, wff_num l → wff_num (l ++ [L.S])
| wff_v : forall l : L_formula, wff_var l → wff_num l

inductive wff_arith : L_formula → Prop where
| wff_num : forall n, wff_num n → wff_arith n
| wff_paren : forall l : L_formula, wff_arith l → wff_arith (L.l_par :: l ++ [L.r_par])
| wff_plus : forall lhs rhs : L_formula, wff_arith lhs → wff_arith rhs → wff_arith (lhs ++ L.plus :: rhs)
| wff_mult : forall lhs rhs : L_formula, wff_arith lhs → wff_arith rhs → wff_arith (lhs ++ L.mult :: rhs)
| wff_exp : forall lhs rhs : L_formula, wff_arith lhs → wff_arith rhs → wff_arith (lhs ++ L.exp :: rhs)

inductive wff: L_formula → Prop where
| wff_paren : forall l : L_formula, wff l → wff (L.l_par :: l ++ [L.r_par])
| wff_eq : forall lhs rhs : L_formula, wff_arith lhs → wff_arith rhs → wff (lhs ++ L.eq :: rhs)
| wff_leq : forall lhs rhs: L_formula, wff_arith lhs → wff_arith rhs → wff (lhs ++ L.leq :: rhs)
| wff_not : forall l : L_formula, wff l → wff (L.not :: l)
| wff_and : forall (lhs rhs : L_formula), wff lhs → wff rhs → wff (lhs ++ L.and :: rhs)
| wff_or  : forall (lhs rhs : L_formula), wff lhs → wff rhs → wff (lhs ++ L.or :: rhs)
| wff_imp : forall (lhs rhs : L_formula), wff lhs → wff rhs → wff (lhs ++ L.imp :: rhs)
| wff_all : forall v : L_formula, forall l : L_formula, wff l → wff_var v →
              wff ([L.all] ++ v ++ l)
| wff_exi : forall v : L_formula, forall l : L_formula, wff l → wff_var v →
              wff ([L.exi] ++ v ++ l)

theorem countPrimes_replicate (m: Nat):
  countPrimes (List.replicate m L.prime) = (m, []) := by
  induction m with
  | zero => simp
  | succ n ih =>
    simp [List.replicate, ih]

theorem countPrimes_replicate_S_tail (k : Nat) :
    countPrimes (List.replicate k L.S) = (0, List.replicate k L.S) := by
  cases k <;> simp [countPrimes, List.replicate]

theorem countPrimes_replicate_S (m k : Nat) :
    countPrimes (List.replicate m L.prime ++ List.replicate k L.S) =
      (m, List.replicate k L.S) := by
  induction m with
  | zero =>
      simpa using countPrimes_replicate_S_tail k
  | succ m ih =>
      simp [List.replicate, countPrimes, ih]

theorem parseVar_replicate:
  forall m, parseVar (L.var :: List.replicate m L.prime) = some (.var m, []) := by
  intro m
  simp [countPrimes_replicate]

theorem wff_var_parseVar_some:
  forall l,
    wff_var l →
    exists n, parseVar l = some (n, []) := by
  intros l h
  rcases h with ⟨n, h⟩
  subst h
  exists (.var n)
  simp [countPrimes_replicate]

theorem wff_num_unparse :
  ∀ l, wff_num l → ∃ n, l = unparse_num n := by
  intro l h
  induction h with
  | wff_O =>
      exact ⟨Num.zero, rfl⟩
  | wff_v l hv =>
      rcases hv with ⟨m, rfl⟩
      exact ⟨Num.var m, rfl⟩
  | wff_S l h ih =>
      rcases ih with ⟨n, rfl⟩
      exact ⟨Num.succ n, rfl⟩


theorem unparse_num_wff : forall (n : Num),
  wff_num (unparse_num n) := by
  intro n
  induction n with
  | zero =>
    simp
    apply wff_num.wff_O
  | var nᵥ =>
    simp
    apply wff_num.wff_v
    exists nᵥ
  | succ n ih =>
    simp
    apply wff_num.wff_S
    assumption


theorem unparse_term_wff : forall (t : Term),
  wff_arith (unparse_term t) := by
  intro t
  induction t <;> simp at *
  case num n =>
    apply wff_arith.wff_num
    exact unparse_num_wff n
  case add n m ih1 ih2 =>
    have h1 : (unparse_term n ++ L.plus :: (unparse_term m ++ [L.r_par]))
            = (unparse_term n ++ L.plus :: unparse_term m) ++ [L.r_par] := by grind
    rw [h1]
    apply wff_arith.wff_paren
    apply wff_arith.wff_plus _ _ ih1 ih2
  case mul n m ih1 ih2 =>
    have h1 : (unparse_term n ++ L.mult :: (unparse_term m ++ [L.r_par]))
            = (unparse_term n ++ L.mult :: unparse_term m) ++ [L.r_par] := by grind
    rw [h1]
    apply wff_arith.wff_paren
    apply wff_arith.wff_mult _ _ ih1 ih2
  case exp n m ih1 ih2 =>
    have h1 : (unparse_term n ++ L.exp :: (unparse_term m ++ [L.r_par]))
            = (unparse_term n ++ L.exp :: unparse_term m) ++ [L.r_par] := by grind
    rw [h1]
    apply wff_arith.wff_paren
    apply wff_arith.wff_exp _ _ ih1 ih2

theorem unparse_wff : forall (t : Formula) (l : L_formula),
  unparse t = l → wff l := by
  intro t
  induction t <;> intros l h <;> simp at * <;> rw [←h]
  case eq lhs rhs =>
    apply wff.wff_eq <;> apply unparse_term_wff
  case le lhs rhs =>
    apply wff.wff_leq <;> apply unparse_term_wff
  case not p ih =>
    apply wff.wff_not
    apply wff.wff_paren
    assumption
  case and p q ih1 ih2 =>
    have h1 : (L.l_par :: (unparse p ++ L.and :: (unparse q ++ [L.r_par])))
            = (L.l_par :: (unparse p ++ L.and :: unparse q) ++ [L.r_par]) := by grind
    rw [h1]
    apply wff.wff_paren
    apply wff.wff_and <;> assumption

  case or p q ih1 ih2 =>
    have h1 : (L.l_par :: (unparse p ++ L.or :: (unparse q ++ [L.r_par])))
            = (L.l_par :: (unparse p ++ L.or :: unparse q) ++ [L.r_par]) := by grind
    rw [h1]
    apply wff.wff_paren
    apply wff.wff_or <;> assumption

  case imp p q ih1 ih2 =>
    have h1 : (L.l_par :: (unparse p ++ L.imp :: (unparse q ++ [L.r_par])))
            = (L.l_par :: (unparse p ++ L.imp :: unparse q) ++ [L.r_par]) := by grind
    rw [h1]
    apply wff.wff_paren
    apply wff.wff_imp <;> assumption

  case forall_ n p ih2 =>
    have h1 : (L.all :: L.var :: (List.replicate n L.prime ++ L.l_par :: (unparse p ++ [L.r_par])))
            = (L.all :: (L.var :: List.replicate n L.prime) ++ L.l_par :: (unparse p ++ [L.r_par])) := by grind
    rw [h1]
    apply wff.wff_all
    have h2 : (L.l_par :: (unparse p ++ [L.r_par]))
            = (L.l_par :: unparse p) ++ [L.r_par] := by grind
    rw [h2]
    apply wff.wff_paren
    assumption
    exists n

  case exists_ n p ih2 =>
    have h1 : (L.exi :: L.var :: (List.replicate n L.prime ++ L.l_par :: (unparse p ++ [L.r_par])))
            = (L.exi :: (L.var :: List.replicate n L.prime) ++ L.l_par :: (unparse p ++ [L.r_par])) := by grind
    rw [h1]
    apply wff.wff_exi
    have h2 : (L.l_par :: (unparse p ++ [L.r_par]))
            = (L.l_par :: unparse p) ++ [L.r_par] := by grind
    rw [h2]
    apply wff.wff_paren
    assumption
    exists n


section parseDeterministic

-- theorem parseTerm_nil : forall fuel,
--   parseTerm fuel [] = none := by
--   intro fuel
--   induction fuel
--   case zero =>
--     simp
--   case succ n m =>
--     simp [parseTerm] at *

theorem parseVar_det :
  ∀ l r1 r2,
    parseVar l = some r1 →
    parseVar l = some r2 →
    r1 = r2 := by
  intro l r1 r2 h1 h2
  obtain ⟨n1, r1⟩ := r1
  obtain ⟨n2, r2⟩ := r2
  rw [h1] at h2
  injection h2 with h2

mutual

theorem parseAtom_succ :
    ∀ {fuel xs r},
      parseTerm.parseAtom fuel xs = some r →
      parseTerm.parseAtom (fuel + 1) xs = some r := by
  intro fuel xs r h
  cases fuel with
  | zero =>
    simp [parseTerm.parseAtom] at h
  | succ fuel =>
    cases xs with
    | nil => simp [parseTerm.parseAtom] at *
    | cons a xs =>
      cases a <;> simp [parseTerm.parseAtom] at * <;> try assumption
      case l_par =>
        cases hAdd : parseTerm.parseAdd fuel xs <;> simp [hAdd] at h
        rename_i p
        obtain ⟨t, rest⟩ := p
        cases rest with
        | nil => simp at h
        | cons b ys =>
          cases b <;> try (simp at h)
          subst h
          have hAdd' :
            parseTerm.parseAdd (fuel + 1) xs = some (t, L.r_par :: ys) := by
              apply parseAdd_succ
              assumption
          simp [hAdd']
termination_by fuel _ _ => (fuel, 0)
decreasing_by
  subst_vars
  simp_wf
  omega

theorem parseSuccLoop_succ :
    ∀ {fuel t xs r},
      parseTerm.parseSuccLoop fuel t xs = some r →
      parseTerm.parseSuccLoop (fuel + 1) t xs = some r := by
  intro fuel t xs r h
  cases xs with
  | nil =>
      simpa [parseTerm.parseSuccLoop] using h
  | cons a xs =>
      cases a <;> try (simpa [parseTerm.parseSuccLoop] using h)
      case S =>
        cases fuel with
        | zero =>
            simp [parseTerm.parseSuccLoop] at h
        | succ fuel =>
            cases t <;> try (simpa [parseTerm.parseSuccLoop] using h)
            case num n =>
              have hLoop : parseTerm.parseSuccLoop fuel (.num (.succ n)) xs = some r := by
                simpa [parseTerm.parseSuccLoop] using h
              have hLoop' : parseTerm.parseSuccLoop (fuel + 1) (.num (.succ n)) xs = some r :=
                parseSuccLoop_succ hLoop
              simpa [parseTerm.parseSuccLoop] using hLoop'
termination_by fuel _ _ _ => (fuel, 1)
decreasing_by
  subst_vars
  · apply Prod.Lex.left
    omega

theorem parseSucc_succ :
    ∀ {fuel xs r},
      parseTerm.parseSucc fuel xs = some r →
      parseTerm.parseSucc (fuel + 1) xs = some r := by
  intro fuel xs r h
  cases fuel with
  | zero =>
      simp [parseTerm.parseSucc, parseTerm.parseAtom] at h
  | succ fuel =>
      cases hA : parseTerm.parseAtom (fuel + 1) xs with
      | none =>
          simp [parseTerm.parseSucc, hA] at h
      | some p =>
          obtain ⟨t, rest⟩ := p
          have hLoop : parseTerm.parseSuccLoop (fuel + 1) t rest = some r := by
            simpa [parseTerm.parseSucc, hA] using h
          have hA' : parseTerm.parseAtom ((fuel + 1) + 1) xs = some (t, rest) :=
            parseAtom_succ hA
          have hLoop' : parseTerm.parseSuccLoop ((fuel + 1) + 1) t rest = some r :=
            parseSuccLoop_succ hLoop
          simpa [parseTerm.parseSucc, hA', Nat.add_assoc] using hLoop'
termination_by fuel _ _ => (fuel, 2)
decreasing_by
  subst_vars
  refine Prod.Lex.right ?_ ?_
  omega

theorem parseExp_succ :
    ∀ {fuel xs r},
      parseTerm.parseExp fuel xs = some r →
      parseTerm.parseExp (fuel + 1) xs = some r := by
  intro fuel xs r h
  cases fuel with
  | zero =>
      simp [parseTerm.parseExp] at h
  | succ fuel =>
      cases hS : parseTerm.parseSucc fuel xs with
      | none =>
          simp [parseTerm.parseExp, hS] at h
      | some p =>
          obtain ⟨lhs, rest⟩ := p
          have hS' : parseTerm.parseSucc (fuel + 1) xs = some (lhs, rest) :=
            parseSucc_succ hS
          cases rest with
          | nil =>
              simp [parseTerm.parseExp, hS] at h
              simpa [parseTerm.parseExp, hS'] using h
          | cons a ys =>
              cases a
              case exp =>
                cases hE : parseTerm.parseExp fuel ys with
                | none =>
                    simp [parseTerm.parseExp, hS, hE] at h
                | some q =>
                    obtain ⟨rhs, zs⟩ := q
                    have hE' : parseTerm.parseExp (fuel + 1) ys = some (rhs, zs) :=
                      parseExp_succ hE
                    simp [parseTerm.parseExp, hS, hE] at h
                    subst r
                    rw [parseTerm.parseExp, hS']
                    simp [hE']
              all_goals
                simp [parseTerm.parseExp, hS] at h
                simpa [parseTerm.parseExp, hS'] using h
termination_by fuel _ _ => (fuel, 3)
decreasing_by
  subst_vars
  · apply Prod.Lex.left
    omega
  · apply Prod.Lex.left
    omega

theorem parseMulLoop_succ :
    ∀ {fuel acc xs r},
      parseTerm.parseMulLoop fuel acc xs = some r →
      parseTerm.parseMulLoop (fuel + 1) acc xs = some r := by
  intro fuel acc xs r h
  cases xs with
  | nil =>
      cases fuel <;> simp [parseTerm.parseMulLoop] at * <;> try assumption
  | cons a xs =>
      cases a
      case mult =>
        cases fuel with
        | zero =>
            simp [parseTerm.parseMulLoop] at h
        | succ fuel =>
            cases hE : parseTerm.parseExp fuel xs with
            | none =>
                simp [parseTerm.parseMulLoop, hE] at h
            | some p =>
                obtain ⟨rhs, zs⟩ := p
                have hLoop : parseTerm.parseMulLoop fuel (.mul acc rhs) zs = some r := by
                  simpa [parseTerm.parseMulLoop, hE] using h
                have hE' : parseTerm.parseExp (fuel + 1) xs = some (rhs, zs) :=
                  parseExp_succ hE
                have hLoop' : parseTerm.parseMulLoop (fuel + 1) (.mul acc rhs) zs = some r :=
                  parseMulLoop_succ hLoop
                simpa [parseTerm.parseMulLoop, hE'] using hLoop'
      all_goals
        cases fuel <;> simpa [parseTerm.parseMulLoop] using h
termination_by fuel _ _ _ => (fuel, 4)
decreasing_by
  subst_vars
  · apply Prod.Lex.left
    omega
  · apply Prod.Lex.left
    omega

theorem parseMul_succ :
    ∀ {fuel xs r},
      parseTerm.parseMul fuel xs = some r →
      parseTerm.parseMul (fuel + 1) xs = some r := by
  intro fuel xs r h
  cases fuel with
  | zero =>
      simp [parseTerm.parseMul] at h
  | succ fuel =>
      cases hE : parseTerm.parseExp (fuel + 1) xs with
      | none =>
          simp [parseTerm.parseMul, hE] at h
      | some p =>
          obtain ⟨lhs, rest⟩ := p
          have hLoop : parseTerm.parseMulLoop (fuel + 1) lhs rest = some r := by
            simpa [parseTerm.parseMul, hE] using h
          have hE' : parseTerm.parseExp ((fuel + 1) + 1) xs = some (lhs, rest) :=
            parseExp_succ hE
          have hLoop' : parseTerm.parseMulLoop ((fuel + 1) + 1) lhs rest = some r :=
            parseMulLoop_succ hLoop
          simpa [parseTerm.parseMul, hE', Nat.add_assoc] using hLoop'
termination_by fuel _ _ => (fuel, 5)
decreasing_by
  subst_vars
  · apply Prod.Lex.right
    omega
  · subst_vars
    apply Prod.Lex.right
    omega

theorem parseAddLoop_succ :
    ∀ {fuel acc xs r},
      parseTerm.parseAddLoop fuel acc xs = some r →
      parseTerm.parseAddLoop (fuel + 1) acc xs = some r := by
  intro fuel acc xs r h
  cases xs with
  | nil =>
      cases fuel <;> simp [parseTerm.parseAddLoop] at * <;> try assumption
  | cons a xs =>
      cases a <;> try (simpa [parseTerm.parseAddLoop] using h)
      case plus =>
        cases fuel with
        | zero =>
            simp [parseTerm.parseAddLoop] at h
        | succ fuel =>
            cases hM : parseTerm.parseMul fuel xs with
            | none =>
                simp [parseTerm.parseAddLoop, hM] at h
            | some p =>
                obtain ⟨rhs, zs⟩ := p
                have hLoop : parseTerm.parseAddLoop fuel (.add acc rhs) zs = some r := by
                  simpa [parseTerm.parseAddLoop, hM] using h
                have hM' : parseTerm.parseMul (fuel + 1) xs = some (rhs, zs) := parseMul_succ hM
                have hLoop' : parseTerm.parseAddLoop (fuel + 1) (.add acc rhs) zs = some r := parseAddLoop_succ hLoop
                simpa [parseTerm.parseAddLoop, hM'] using hLoop'
      all_goals
        cases fuel <;> simpa [parseTerm.parseAddLoop] using h
termination_by fuel _ _ _ => (fuel, 6)
decreasing_by
  subst_vars
  · apply Prod.Lex.left
    omega
  · apply Prod.Lex.left
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
      obtain ⟨lhs, rest⟩ := p
      have hLoop : parseTerm.parseAddLoop (fuel + 1) lhs rest = some r := by
        simpa [parseTerm.parseAdd, hM] using h
      have hM' : parseTerm.parseMul ((fuel + 1) + 1) xs = some (lhs, rest) := parseMul_succ hM
      have hLoop' : parseTerm.parseAddLoop ((fuel + 1) + 1) lhs rest = some r := parseAddLoop_succ hLoop
      simpa [parseTerm.parseAdd, hM', Nat.add_assoc] using hLoop'
termination_by fuel _ _ => (fuel, 7)
decreasing_by
  subst_vars
  · refine Prod.Lex.right ?_ ?_
    omega
  · subst_vars
    apply Prod.Lex.right
    omega

end

theorem parseTerm_succ :
    ∀ {fuel xs r},
      parseTerm fuel xs = some r →
      parseTerm (fuel + 1) xs = some r := by
  intro fuel xs r h
  simpa [parseTerm] using (parseAdd_succ h)

theorem parseTerm_mono
    {fuel₁ fuel₂ : Nat} {xs : L_formula} {r : Term × L_formula}
    (h₁₂ : fuel₁ ≤ fuel₂)
    (h : parseTerm fuel₁ xs = some r) :
    parseTerm fuel₂ xs = some r := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h₁₂
  induction d generalizing fuel₁ with
  | zero =>
      simpa using h
  | succ d ih =>
      have h2 : fuel₁ ≤ fuel₁ + d := by omega
      have h' : parseTerm (fuel₁ + d) xs = some r := ih h h2
      simpa [Nat.add_assoc] using (parseTerm_succ h')

theorem parseTerm_det_sameFuel
    {fuel : Nat} {xs : L_formula} {r₁ r₂ : Term × L_formula}
    (h1 : parseTerm fuel xs = some r₁)
    (h2 : parseTerm fuel xs = some r₂) :
    r₁ = r₂ := by
  rw [h1] at h2
  injection h2 with h

theorem parseTerm_det_diff_fuel
    {fuel₁ fuel₂ : Nat} {xs : L_formula} {r₁ r₂ : Term × L_formula}
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

end parseDeterministic

theorem parseSuccLoop_replicate_S :
    ∀ (k : Nat) (n₀ : Num), ∃ n fuel,
      parseTerm.parseSuccLoop fuel (.num n₀) (List.replicate k L.S) = some (.num n, []) := by
  intro k
  induction k with
  | zero =>
      intro n₀
      refine ⟨n₀, 0, ?_⟩
      simp [parseTerm.parseSuccLoop]
  | succ k ih =>
      intro n₀
      rcases ih (.succ n₀) with ⟨n, fuel, h⟩
      refine ⟨n, fuel + 1, ?_⟩
      simp [List.replicate, parseTerm.parseSuccLoop, h]

theorem replicate_S_append_one (k : Nat) :
    List.replicate (k + 1) L.S = List.replicate k L.S ++ [L.S] := by
  induction k with
  | zero =>
      simp [List.replicate]
  | succ k ih =>
      simp [List.replicate] at *
      rw [ih]

theorem wff_num_shape :
    ∀ l, wff_num l →
      ∃ base k, (((base = [L.O]) ∨ wff_var base) ∧
        l = base ++ List.replicate k L.S) := by
  intro l h
  induction h with
  | wff_O =>
      refine ⟨[L.O], 0, ?_⟩
      simp [wff_var]
  | wff_v l hv =>
      refine ⟨l, 0, ?_⟩
      simp [hv]
  | wff_S l hl ih =>
      rcases ih with ⟨base, k, hbase, hk⟩
      refine ⟨base, k + 1, ?_⟩
      constructor
      · exact hbase
      · rw [hk, replicate_S_append_one]
        simp [List.append_assoc]


theorem wff_var_parseNum_some:
  forall l,
  wff_num l →
  exists fuel n, parseTerm fuel l = some (Term.num n, []) := by
  intro l h
  rcases wff_num_shape l h with ⟨base, k, hbase, rfl⟩
  cases hbase with
  | inl hO =>
      subst hO
      rcases parseSuccLoop_replicate_S k Num.zero with ⟨n, fuel, hLoop⟩
      have hLoop' :
          parseTerm.parseSuccLoop (fuel + 1) (.num .zero) (List.replicate k L.S) =
            some (.num n, []) := by
        exact parseSuccLoop_succ hLoop
      refine ⟨fuel + 2, n, ?_⟩
      simp [parseTerm, parseTerm.parseAdd, parseTerm.parseMul, parseTerm.parseExp,
            parseTerm.parseSucc, parseTerm.parseAtom, parseTerm.parseMulLoop, parseTerm.parseAddLoop, hLoop']

  | inr hv =>
      rcases hv with ⟨m, rfl⟩
      rcases parseSuccLoop_replicate_S k (.var m) with ⟨n, fuel, hLoop⟩
      have hLoop' :
          parseTerm.parseSuccLoop (fuel + 1) (.num (.var m)) (List.replicate k L.S) =
            some (.num n, []) := by
        exact parseSuccLoop_succ hLoop
      have hcp :
          countPrimes (List.replicate m L.prime ++ List.replicate k L.S) =
            (m, List.replicate k L.S) := by
        simpa using countPrimes_replicate_S m k
      refine ⟨fuel + 2, n, ?_⟩
      simp [parseTerm, parseTerm.parseAdd, parseTerm.parseMul, parseTerm.parseExp,
            parseTerm.parseSucc, parseTerm.parseAtom, parseTerm.parseMulLoop, parseTerm.parseAddLoop, hcp, hLoop']

theorem parseTerm_append_rpar
    {fuel : Nat} {l : L_formula} {t : Term}
    (h : parseTerm fuel l = some (t, [])) :
    parseTerm fuel (l ++ [L.r_par]) = some (t, [L.r_par]) := by
  sorry

theorem parseTerm_append_plus
    {fuel : Nat} {l r : L_formula} {t : Term}
    (h : parseTerm fuel l = some (t, [])) :
    parseTerm fuel (l ++ [L.plus] ++ r) = some (t, L.plus :: r) := by
  sorry

theorem parseTerm_plus_closed
    {l₁ l₂ : L_formula} {t₁ t₂ : Term}
    (h₁ : ∃ fuel, parseTerm fuel l₁ = some (t₁, []))
    (h₂ : ∃ fuel, parseTerm fuel l₂ = some (t₂, [])) :
    ∃ fuel, parseTerm fuel (l₁ ++ [L.plus] ++ l₂) = some (Term.add t₁ t₂, []) := by
  sorry

theorem wff_parseTerm : forall l,
  wff_arith l →
  exists fuel φ, parseTerm fuel l = some (φ, []) := by
  intros l h
  induction h with
  | wff_num n ih=>
    have ⟨fuel, m, h⟩:= wff_var_parseNum_some _ ih
    exists fuel
    exists Term.num m
  | wff_paren l h ih =>
    rcases ih with ⟨fuel, t, hparse⟩
    have hinner : parseTerm fuel (l ++ [L.r_par]) = some (t, [L.r_par]) := by
      exact parseTerm_append_rpar hparse
    have hAdd :
        parseTerm.parseAdd fuel (l ++ [L.r_par]) = some (t, [L.r_par]) := by
      simpa [parseTerm] using hinner
    have hAtom :
        parseTerm.parseAtom (fuel + 1) (L.l_par :: (l ++ [L.r_par])) = some (t, []) := by
      simp [parseTerm.parseAtom, hAdd]
    have hSucc :
        parseTerm.parseSucc (fuel + 1) (L.l_par :: (l ++ [L.r_par])) = some (t, []) := by
      simp [parseTerm.parseSucc, hAtom, parseTerm.parseSuccLoop]
    have hExp :
        parseTerm.parseExp (fuel + 2) (L.l_par :: (l ++ [L.r_par])) = some (t, []) := by
      simp [parseTerm.parseExp, hSucc]
    have hMul :
        parseTerm.parseMul (fuel + 2) (L.l_par :: (l ++ [L.r_par])) = some (t, []) := by
      simp [parseTerm.parseMul, hExp, parseTerm.parseMulLoop]
    refine ⟨fuel + 2, t, ?_⟩
    simp [parseTerm, parseTerm.parseAdd, hMul, parseTerm.parseAddLoop, List.cons_append]

  | wff_plus l₁ l₂ hl hr ihl ihr =>
    rcases ihl with ⟨fuel₁, t₁, h₁⟩
    rcases ihr with ⟨fuel₂, t₂, h₂⟩
    rcases parseTerm_plus_closed ⟨fuel₁, h₁⟩ ⟨fuel₂, h₂⟩ with ⟨fuel, hplus⟩
    -- rcases parseTerm_plus_closed h₁ h₂ with ⟨fuel, hplus⟩
    exists fuel
    exists (Term.add t₁ t₂)
    simp at hplus
    assumption

  | wff_mult lhs rhs hl hr ihl ihr  => sorry
  | wff_exp lhs rhs hl hr ihl ihr  => sorry

theorem wff_parse : forall l,
  wff l →
  exists fuel φ, parse fuel l = some φ := by sorry

theorem parse_sound :
  ∀ {fuel l φ}, parse fuel l = some φ → unparse φ = l := by
  sorry

theorem unparse_injective :
  unparse ψ = unparse φ → ψ = φ:= by²
  sorry


theorem unparse_parse_closed :
    ∀ φ, ∃ fuel, parseFormula fuel (unparse φ) = some (φ, []) := by
  intro φ
  have h: wff (unparse φ):= by
    have := unparse_wff φ
    exact this (unparse φ) rfl
  rcases wff_parse (unparse φ) h with ⟨fuel, ψ, hparse⟩
  have hs : unparse ψ  = unparse φ := by
    simpa using parse_sound hparse
  have hψ : ψ = φ := by
    exact unparse_injective hs
  exists fuel
  subst hψ
  simp at *
  cases h : parseFormula.parseNot fuel (unparse ψ)
  · simp [h] at hparse
  · grind

theorem unparse_parse_id : forall φ l,
  unparse φ = l → exists fuel, parse fuel l = some φ := by
  intro φ l h
  cases h
  rcases unparse_parse_closed φ with ⟨fuel, hparse⟩
  refine ⟨fuel, ?_⟩
  have hparse' : parseFormula.parseNot fuel (unparse φ) = some (φ, []) := by
    simpa [parseFormula] using hparse
  simp [parse, hparse']
