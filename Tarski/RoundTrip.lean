import Tarski.ParseMono

open Lang

/-!
# Phase 2 — the round-trip theorem `parse (unparse φ) = some φ`
-/

/-! ## Generic fuel monotonicity -/

theorem fuel_mono {α : Type} {P : Nat → Option α}
    (hs : ∀ n r, P n = some r → P (n + 1) = some r) :
    ∀ {m n : Nat} {r : α}, m ≤ n → P m = some r → P n = some r := by
  intro m n r hmn h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction d with
  | zero => simpa using h
  | succ d ih => exact hs _ _ ih

theorem parseAtom_mono {m n : Nat} {xs : L_formula} {r : Term × L_formula}
    (hmn : m ≤ n) (h : parseTerm.parseAtom m xs = some r) :
    parseTerm.parseAtom n xs = some r :=
  fuel_mono (P := fun f => parseTerm.parseAtom f xs) (fun _ _ h => parseAtom_succ h) hmn h

theorem parseSuccLoop_mono {m n : Nat} {t : Term} {xs : L_formula} {r : Term × L_formula}
    (hmn : m ≤ n) (h : parseTerm.parseSuccLoop m t xs = some r) :
    parseTerm.parseSuccLoop n t xs = some r :=
  fuel_mono (P := fun f => parseTerm.parseSuccLoop f t xs)
    (fun _ _ h => parseSuccLoop_succ h) hmn h

theorem parseSucc_mono {m n : Nat} {xs : L_formula} {r : Term × L_formula}
    (hmn : m ≤ n) (h : parseTerm.parseSucc m xs = some r) :
    parseTerm.parseSucc n xs = some r :=
  fuel_mono (P := fun f => parseTerm.parseSucc f xs) (fun _ _ h => parseSucc_succ h) hmn h

theorem parseExp_mono {m n : Nat} {xs : L_formula} {r : Term × L_formula}
    (hmn : m ≤ n) (h : parseTerm.parseExp m xs = some r) :
    parseTerm.parseExp n xs = some r :=
  fuel_mono (P := fun f => parseTerm.parseExp f xs) (fun _ _ h => parseExp_succ h) hmn h

theorem parseMul_mono {m n : Nat} {xs : L_formula} {r : Term × L_formula}
    (hmn : m ≤ n) (h : parseTerm.parseMul m xs = some r) :
    parseTerm.parseMul n xs = some r :=
  fuel_mono (P := fun f => parseTerm.parseMul f xs) (fun _ _ h => parseMul_succ h) hmn h

theorem parseMulLoop_mono {m n : Nat} {t : Term} {xs : L_formula} {r : Term × L_formula}
    (hmn : m ≤ n) (h : parseTerm.parseMulLoop m t xs = some r) :
    parseTerm.parseMulLoop n t xs = some r :=
  fuel_mono (P := fun f => parseTerm.parseMulLoop f t xs)
    (fun _ _ h => parseMulLoop_succ h) hmn h

theorem parseAdd_mono {m n : Nat} {xs : L_formula} {r : Term × L_formula}
    (hmn : m ≤ n) (h : parseTerm.parseAdd m xs = some r) :
    parseTerm.parseAdd n xs = some r :=
  fuel_mono (P := fun f => parseTerm.parseAdd f xs) (fun _ _ h => parseAdd_succ h) hmn h

theorem parseAddLoop_mono {m n : Nat} {t : Term} {xs : L_formula} {r : Term × L_formula}
    (hmn : m ≤ n) (h : parseTerm.parseAddLoop m t xs = some r) :
    parseTerm.parseAddLoop n t xs = some r :=
  fuel_mono (P := fun f => parseTerm.parseAddLoop f t xs)
    (fun _ _ h => parseAddLoop_succ h) hmn h

/-! ## Safe continuations for the term parser

Each precedence level of `parseTerm` keeps consuming input when it sees a
particular token; a continuation is "safe" for that level when it starts with
none of the tokens that would let the level continue. -/

@[simp]
def safeAtom : L_formula → Prop
  | L.prime :: _ => False
  | _ => True

@[simp]
def safeSucc : L_formula → Prop
  | L.prime :: _ => False
  | L.S :: _ => False
  | _ => True

@[simp]
def safeExp : L_formula → Prop
  | L.prime :: _ => False
  | L.S :: _ => False
  | L.exp :: _ => False
  | _ => True

@[simp]
def safeMul : L_formula → Prop
  | L.prime :: _ => False
  | L.S :: _ => False
  | L.exp :: _ => False
  | L.mult :: _ => False
  | _ => True

@[simp]
def termSafe : L_formula → Prop
  | L.prime :: _ => False
  | L.S :: _ => False
  | L.exp :: _ => False
  | L.mult :: _ => False
  | L.plus :: _ => False
  | _ => True

theorem safeSucc_atom {l : L_formula} (h : safeSucc l) : safeAtom l := by
  cases l with
  | nil => trivial
  | cons a l => cases a <;> simp_all

theorem safeExp_succ {l : L_formula} (h : safeExp l) : safeSucc l := by
  cases l with
  | nil => trivial
  | cons a l => cases a <;> simp_all

theorem safeMul_exp {l : L_formula} (h : safeMul l) : safeExp l := by
  cases l with
  | nil => trivial
  | cons a l => cases a <;> simp_all

theorem termSafe_mul {l : L_formula} (h : termSafe l) : safeMul l := by
  cases l with
  | nil => trivial
  | cons a l => cases a <;> simp_all

theorem termSafe_exp {l : L_formula} (h : termSafe l) : safeExp l :=
  safeMul_exp (termSafe_mul h)

theorem termSafe_succ {l : L_formula} (h : termSafe l) : safeSucc l :=
  safeExp_succ (termSafe_exp h)

theorem termSafe_atom {l : L_formula} (h : termSafe l) : safeAtom l :=
  safeSucc_atom (termSafe_succ h)

/-! ## Basic shape lemmas -/

def succIter : Nat → Term → Term
  | 0, t => t
  | k + 1, t => succIter k (.succ t)

theorem countPrimes_safeAtom {rest : L_formula} (h : safeAtom rest) :
    countPrimes rest = (0, rest) := by
  cases rest with
  | nil => simp
  | cons a l => cases a <;> simp_all

theorem countPrimes_append (m : Nat) {rest : L_formula} (h : safeAtom rest) :
    countPrimes (List.replicate m L.prime ++ rest) = (m, rest) := by
  induction m with
  | zero => simpa using countPrimes_safeAtom h
  | succ m ih => simp [List.replicate_succ, ih]

theorem safeAtom_replicateS (k : Nat) {rest : L_formula} (h : safeAtom rest) :
    safeAtom (List.replicate k L.S ++ rest) := by
  cases k with
  | zero => simpa using h
  | succ k => simp [List.replicate_succ]

theorem parseSuccLoop_replicate (k : Nat) (t : Term) {rest : L_formula} (h : safeSucc rest) :
    parseTerm.parseSuccLoop k t (List.replicate k L.S ++ rest) = some (succIter k t, rest) := by
  induction k generalizing t with
  | zero =>
      simp only [List.replicate, List.nil_append, succIter]
      cases rest with
      | nil => rfl
      | cons a l => cases a <;> simp_all [parseTerm.parseSuccLoop]
  | succ k ih =>
      simp only [List.replicate_succ, List.cons_append, succIter,
        parseTerm.parseSuccLoop]
      exact ih (.succ t)

/-! ## The precedence cascade

`XOK t` says: the level-`X` parser, run on `unparse_term t` followed by `k`
successor symbols and any continuation safe for that level, returns exactly
`succ^k t` and the continuation. -/

def SuccOK (t : Term) : Prop :=
  ∀ (k : Nat) (rest : L_formula), safeSucc rest →
    ∃ f, parseTerm.parseSucc f (unparse_term t ++ (List.replicate k L.S ++ rest))
          = some (succIter k t, rest)

def ExpOK (t : Term) : Prop :=
  ∀ (k : Nat) (rest : L_formula), safeExp rest →
    ∃ f, parseTerm.parseExp f (unparse_term t ++ (List.replicate k L.S ++ rest))
          = some (succIter k t, rest)

def MulOK (t : Term) : Prop :=
  ∀ (k : Nat) (rest : L_formula), safeMul rest →
    ∃ f, parseTerm.parseMul f (unparse_term t ++ (List.replicate k L.S ++ rest))
          = some (succIter k t, rest)

def AddOK (t : Term) : Prop :=
  ∀ (k : Nat) (rest : L_formula), termSafe rest →
    ∃ f, parseTerm.parseAdd f (unparse_term t ++ (List.replicate k L.S ++ rest))
          = some (succIter k t, rest)

theorem expOK_of_succOK {t : Term} (hS : SuccOK t) : ExpOK t := by
  intro k rest h
  obtain ⟨f, hf⟩ := hS k rest (safeExp_succ h)
  refine ⟨f + 1, ?_⟩
  cases rest with
  | nil =>
      simp only [List.append_nil] at hf
      simp [parseTerm.parseExp, hf]
  | cons a l => cases a <;> simp_all [parseTerm.parseExp]

theorem mulOK_of_expOK {t : Term} (hE : ExpOK t) : MulOK t := by
  intro k rest h
  obtain ⟨f, hf⟩ := hE k rest (safeMul_exp h)
  have hf' := parseExp_mono (Nat.le_succ f) hf
  clear hf
  refine ⟨f + 1, ?_⟩
  cases rest with
  | nil =>
      simp only [List.append_nil] at hf'
      simp [parseTerm.parseMul, parseTerm.parseMulLoop, hf']
  | cons a l => cases a <;> simp_all [parseTerm.parseMul, parseTerm.parseMulLoop]

theorem addOK_of_mulOK {t : Term} (hM : MulOK t) : AddOK t := by
  intro k rest h
  obtain ⟨f, hf⟩ := hM k rest (termSafe_mul h)
  have hf' := parseMul_mono (Nat.le_succ f) hf
  clear hf
  refine ⟨f + 1, ?_⟩
  cases rest with
  | nil =>
      simp only [List.append_nil] at hf'
      simp [parseTerm.parseAdd, parseTerm.parseAddLoop, hf']
  | cons a l => cases a <;> simp_all [parseTerm.parseAdd, parseTerm.parseAddLoop]

theorem succOK_zero {t : Term} (h : SuccOK t) {rest : L_formula} (hr : safeSucc rest) :
    ∃ f, parseTerm.parseSucc f (unparse_term t ++ rest) = some (t, rest) := by
  simpa [succIter] using h 0 rest hr

theorem expOK_zero {t : Term} (h : ExpOK t) {rest : L_formula} (hr : safeExp rest) :
    ∃ f, parseTerm.parseExp f (unparse_term t ++ rest) = some (t, rest) := by
  simpa [succIter] using h 0 rest hr

theorem mulOK_zero {t : Term} (h : MulOK t) {rest : L_formula} (hr : safeMul rest) :
    ∃ f, parseTerm.parseMul f (unparse_term t ++ rest) = some (t, rest) := by
  simpa [succIter] using h 0 rest hr

theorem addOK_zero {t : Term} (h : AddOK t) {rest : L_formula} (hr : termSafe rest) :
    ∃ f, parseTerm.parseAdd f (unparse_term t ++ rest) = some (t, rest) := by
  simpa [succIter] using h 0 rest hr

/-! ## The three binary operators, seen from `parseAdd` -/

theorem parseAdd_plus {a b : Term} (ha : MulOK a) (hb : MulOK b) (tail : L_formula) :
    ∃ f, parseTerm.parseAdd f (unparse_term a ++ L.plus :: (unparse_term b ++ L.r_par :: tail))
          = some (Term.add a b, L.r_par :: tail) := by
  obtain ⟨f1, h1⟩ :=
    mulOK_zero ha (rest := L.plus :: (unparse_term b ++ L.r_par :: tail)) (by simp)
  obtain ⟨f2, h2⟩ := mulOK_zero hb (rest := L.r_par :: tail) (by simp)
  refine ⟨f1 + f2 + 2, ?_⟩
  have e1 : parseTerm.parseMul (f1 + f2 + 2)
      (unparse_term a ++ L.plus :: (unparse_term b ++ L.r_par :: tail))
      = some (a, L.plus :: (unparse_term b ++ L.r_par :: tail)) := parseMul_mono (by omega) h1
  have e2 : parseTerm.parseMul (f1 + f2 + 1) (unparse_term b ++ L.r_par :: tail)
      = some (b, L.r_par :: tail) := parseMul_mono (by omega) h2
  simp [parseTerm.parseAdd, parseTerm.parseAddLoop, e1, e2]

theorem parseAdd_mult {a b : Term} (ha : ExpOK a) (hb : ExpOK b) (tail : L_formula) :
    ∃ f, parseTerm.parseAdd f (unparse_term a ++ L.mult :: (unparse_term b ++ L.r_par :: tail))
          = some (Term.mul a b, L.r_par :: tail) := by
  obtain ⟨f1, h1⟩ :=
    expOK_zero ha (rest := L.mult :: (unparse_term b ++ L.r_par :: tail)) (by simp)
  obtain ⟨f2, h2⟩ := expOK_zero hb (rest := L.r_par :: tail) (by simp)
  refine ⟨f1 + f2 + 2, ?_⟩
  have e1 : parseTerm.parseExp (f1 + f2 + 2)
      (unparse_term a ++ L.mult :: (unparse_term b ++ L.r_par :: tail))
      = some (a, L.mult :: (unparse_term b ++ L.r_par :: tail)) := parseExp_mono (by omega) h1
  have e2 : parseTerm.parseExp (f1 + f2 + 1) (unparse_term b ++ L.r_par :: tail)
      = some (b, L.r_par :: tail) := parseExp_mono (by omega) h2
  simp [parseTerm.parseAdd, parseTerm.parseAddLoop, parseTerm.parseMul,
    parseTerm.parseMulLoop, e1, e2]

theorem parseExp_step {f : Nat} {a b : Term} {xs Y tail : L_formula}
    (e1 : parseTerm.parseSucc f xs = some (a, L.exp :: Y))
    (e2 : parseTerm.parseExp f Y = some (b, tail)) :
    parseTerm.parseExp (f + 1) xs = some (Term.exp a b, tail) := by
  simp [parseTerm.parseExp, e1, e2]

theorem parseAdd_exp {a b : Term} (ha : SuccOK a) (hb : ExpOK b) (tail : L_formula) :
    ∃ f, parseTerm.parseAdd f (unparse_term a ++ L.exp :: (unparse_term b ++ L.r_par :: tail))
          = some (Term.exp a b, L.r_par :: tail) := by
  obtain ⟨f1, h1⟩ :=
    succOK_zero ha (rest := L.exp :: (unparse_term b ++ L.r_par :: tail)) (by simp)
  obtain ⟨f2, h2⟩ := expOK_zero hb (rest := L.r_par :: tail) (by simp)
  refine ⟨f1 + f2 + 2, ?_⟩
  have e1 : parseTerm.parseSucc (f1 + f2 + 1)
      (unparse_term a ++ L.exp :: (unparse_term b ++ L.r_par :: tail))
      = some (a, L.exp :: (unparse_term b ++ L.r_par :: tail)) := parseSucc_mono (by omega) h1
  have e2 : parseTerm.parseExp (f1 + f2 + 1) (unparse_term b ++ L.r_par :: tail)
      = some (b, L.r_par :: tail) := parseExp_mono (by omega) h2
  have e3 : parseTerm.parseExp (f1 + f2 + 2)
      (unparse_term a ++ L.exp :: (unparse_term b ++ L.r_par :: tail))
      = some (Term.exp a b, L.r_par :: tail) := parseExp_step e1 e2
  simp [parseTerm.parseAdd, parseTerm.parseAddLoop, parseTerm.parseMul,
    parseTerm.parseMulLoop, e3]

/-! ## Every term round-trips -/

theorem succOK_all : ∀ t : Term, SuccOK t := by
  intro t
  induction t with
  | var n =>
      intro k rest h
      refine ⟨k + 1, ?_⟩
      have hcp : countPrimes (List.replicate n L.prime ++ (List.replicate k L.S ++ rest))
          = (n, List.replicate k L.S ++ rest) :=
        countPrimes_append n (safeAtom_replicateS k (safeSucc_atom h))
      have hloop : parseTerm.parseSuccLoop (k + 1) (Term.var n) (List.replicate k L.S ++ rest)
          = some (succIter k (Term.var n), rest) :=
        parseSuccLoop_mono (by omega) (parseSuccLoop_replicate k (Term.var n) h)
      simp [parseTerm.parseSucc, parseTerm.parseAtom, hcp, hloop]
  | zero =>
      intro k rest h
      refine ⟨k + 1, ?_⟩
      have hloop : parseTerm.parseSuccLoop (k + 1) Term.zero (List.replicate k L.S ++ rest)
          = some (succIter k Term.zero, rest) :=
        parseSuccLoop_mono (by omega) (parseSuccLoop_replicate k Term.zero h)
      simp [parseTerm.parseSucc, parseTerm.parseAtom, hloop]
  | succ t ih =>
      intro k rest h
      obtain ⟨f, hf⟩ := ih (k + 1) rest h
      refine ⟨f, ?_⟩
      simpa [List.replicate_succ, succIter] using hf
  | add a b iha ihb =>
      intro k rest h
      obtain ⟨f, hf⟩ :=
        parseAdd_plus (mulOK_of_expOK (expOK_of_succOK iha))
          (mulOK_of_expOK (expOK_of_succOK ihb)) (List.replicate k L.S ++ rest)
      refine ⟨f + k + 1, ?_⟩
      have hAdd := parseAdd_mono (m := f) (n := f + k) (by omega) hf
      have hAtom : parseTerm.parseAtom (f + k + 1)
          (unparse_term (Term.add a b) ++ (List.replicate k L.S ++ rest))
          = some (Term.add a b, List.replicate k L.S ++ rest) := by
        simp [parseTerm.parseAtom, hAdd]
      have hloop : parseTerm.parseSuccLoop (f + k + 1) (Term.add a b)
          (List.replicate k L.S ++ rest) = some (succIter k (Term.add a b), rest) :=
        parseSuccLoop_mono (by omega) (parseSuccLoop_replicate k (Term.add a b) h)
      simp only [parseTerm.parseSucc]
      rw [hAtom]
      exact hloop
  | mul a b iha ihb =>
      intro k rest h
      obtain ⟨f, hf⟩ :=
        parseAdd_mult (expOK_of_succOK iha) (expOK_of_succOK ihb) (List.replicate k L.S ++ rest)
      refine ⟨f + k + 1, ?_⟩
      have hAdd := parseAdd_mono (m := f) (n := f + k) (by omega) hf
      have hAtom : parseTerm.parseAtom (f + k + 1)
          (unparse_term (Term.mul a b) ++ (List.replicate k L.S ++ rest))
          = some (Term.mul a b, List.replicate k L.S ++ rest) := by
        simp [parseTerm.parseAtom, hAdd]
      have hloop : parseTerm.parseSuccLoop (f + k + 1) (Term.mul a b)
          (List.replicate k L.S ++ rest) = some (succIter k (Term.mul a b), rest) :=
        parseSuccLoop_mono (by omega) (parseSuccLoop_replicate k (Term.mul a b) h)
      simp only [parseTerm.parseSucc]
      rw [hAtom]
      exact hloop
  | exp a b iha ihb =>
      intro k rest h
      obtain ⟨f, hf⟩ :=
        parseAdd_exp iha (expOK_of_succOK ihb) (List.replicate k L.S ++ rest)
      refine ⟨f + k + 1, ?_⟩
      have hAdd := parseAdd_mono (m := f) (n := f + k) (by omega) hf
      have hAtom : parseTerm.parseAtom (f + k + 1)
          (unparse_term (Term.exp a b) ++ (List.replicate k L.S ++ rest))
          = some (Term.exp a b, List.replicate k L.S ++ rest) := by
        simp [parseTerm.parseAtom, hAdd]
      have hloop : parseTerm.parseSuccLoop (f + k + 1) (Term.exp a b)
          (List.replicate k L.S ++ rest) = some (succIter k (Term.exp a b), rest) :=
        parseSuccLoop_mono (by omega) (parseSuccLoop_replicate k (Term.exp a b) h)
      simp only [parseTerm.parseSucc]
      rw [hAtom]
      exact hloop

theorem parseTerm_unparse_term (t : Term) {rest : L_formula} (h : termSafe rest) :
    ∃ f, parseTerm f (unparse_term t ++ rest) = some (t, rest) := by
  obtain ⟨f, hf⟩ := addOK_zero (addOK_of_mulOK (mulOK_of_expOK (expOK_of_succOK (succOK_all t)))) h
  exact ⟨f, hf⟩

/-! ## Safe continuations for the formula parser -/

@[simp]
def formSafe : L_formula → Prop
  | [] => True
  | L.r_par :: _ => True
  | L.and :: _ => True
  | L.or :: _ => True
  | L.imp :: _ => True
  | _ => False

theorem formSafe_termSafe {l : L_formula} (h : formSafe l) : termSafe l := by
  cases l with
  | nil => trivial
  | cons a l => cases a <;> simp_all

theorem termSafe_unparse_term (t : Term) : ∀ rest : L_formula,
    termSafe (unparse_term t ++ rest) := by
  induction t with
  | var n => intro rest; simp
  | zero => intro rest; simp
  | succ t ih => intro rest; simpa using ih (L.S :: rest)
  | add a b _ _ => intro rest; simp
  | mul a b _ _ => intro rest; simp
  | exp a b _ _ => intro rest; simp

/-! ## One step of the formula parser, at symbolic fuel -/

theorem step_eq {f : Nat} {m n : Term} {xs ys rest : L_formula}
    (e1 : parseTerm f xs = some (m, ys)) (e2 : parseTerm f ys = some (n, rest)) :
    parseFormula (f + 2) (L.eq :: xs) = some (Formula.eq m n, rest) := by
  simp [e1, e2]

theorem step_le {f : Nat} {m n : Term} {xs ys rest : L_formula}
    (e1 : parseTerm f xs = some (m, ys)) (e2 : parseTerm f ys = some (n, rest)) :
    parseFormula (f + 2) (L.leq :: xs) = some (Formula.le m n, rest) := by
  simp [e1, e2]

theorem step_not {f : Nat} {p : Formula} {xs rest : L_formula}
    (e : parseFormula f xs = some (p, L.r_par :: rest)) :
    parseFormula (f + 1) (L.not :: L.l_par :: xs) = some (Formula.not p, rest) := by
  have e' : parseFormula.parseNot f xs = some (p, L.r_par :: rest) := by simpa using e
  simp [e']

theorem step_and {f : Nat} {p q : Formula} {xs ys rest : L_formula}
    (e1 : parseFormula f xs = some (p, L.and :: ys))
    (e2 : parseFormula f ys = some (q, L.r_par :: rest)) :
    parseFormula (f + 2) (L.l_par :: xs) = some (Formula.and p q, rest) := by
  have e1' : parseFormula.parseNot f xs = some (p, L.and :: ys) := by simpa using e1
  have e2' : parseFormula.parseNot f ys = some (q, L.r_par :: rest) := by simpa using e2
  simp [e1', e2']

theorem step_or {f : Nat} {p q : Formula} {xs ys rest : L_formula}
    (e1 : parseFormula f xs = some (p, L.or :: ys))
    (e2 : parseFormula f ys = some (q, L.r_par :: rest)) :
    parseFormula (f + 2) (L.l_par :: xs) = some (Formula.or p q, rest) := by
  have e1' : parseFormula.parseNot f xs = some (p, L.or :: ys) := by simpa using e1
  have e2' : parseFormula.parseNot f ys = some (q, L.r_par :: rest) := by simpa using e2
  simp [e1', e2']

theorem step_imp {f : Nat} {p q : Formula} {xs ys rest : L_formula}
    (e1 : parseFormula f xs = some (p, L.imp :: ys))
    (e2 : parseFormula f ys = some (q, L.r_par :: rest)) :
    parseFormula (f + 2) (L.l_par :: xs) = some (Formula.imp p q, rest) := by
  have e1' : parseFormula.parseNot f xs = some (p, L.imp :: ys) := by simpa using e1
  have e2' : parseFormula.parseNot f ys = some (q, L.r_par :: rest) := by simpa using e2
  simp [e1', e2']

theorem step_forall {f k : Nat} {p : Formula} {xs rest : L_formula}
    (e : parseFormula f xs = some (p, L.r_par :: rest)) :
    parseFormula (f + 3) (L.all :: L.var :: (List.replicate k L.prime ++ L.l_par :: xs))
      = some (Formula.forall_ k p, rest) := by
  have e' : parseFormula.parseNot f xs = some (p, L.r_par :: rest) := by simpa using e
  have hcp : countPrimes (List.replicate k L.prime ++ L.l_par :: xs) = (k, L.l_par :: xs) :=
    countPrimes_append k (by simp)
  simp [hcp, e']

theorem step_exists {f k : Nat} {p : Formula} {xs rest : L_formula}
    (e : parseFormula f xs = some (p, L.r_par :: rest)) :
    parseFormula (f + 3) (L.exi :: L.var :: (List.replicate k L.prime ++ L.l_par :: xs))
      = some (Formula.exists_ k p, rest) := by
  have e' : parseFormula.parseNot f xs = some (p, L.r_par :: rest) := by simpa using e
  have hcp : countPrimes (List.replicate k L.prime ++ L.l_par :: xs) = (k, L.l_par :: xs) :=
    countPrimes_append k (by simp)
  simp [hcp, e']

/-! ## Every formula round-trips -/

theorem parseFormula_unparse : ∀ (φ : Formula) (rest : L_formula), formSafe rest →
    ∃ f, parseFormula f (unparse φ ++ rest) = some (φ, rest) := by
  intro φ
  induction φ with
  | eq m n =>
      intro rest h
      obtain ⟨f1, h1⟩ := parseTerm_unparse_term m (termSafe_unparse_term n rest)
      obtain ⟨f2, h2⟩ := parseTerm_unparse_term n (formSafe_termSafe h)
      have e1 := parseTerm_mono (show f1 ≤ f1 + f2 by omega) h1
      have e2 := parseTerm_mono (show f2 ≤ f1 + f2 by omega) h2
      have hlist : unparse (Formula.eq m n) ++ rest
          = L.eq :: (unparse_term m ++ (unparse_term n ++ rest)) := by simp
      exact ⟨f1 + f2 + 2, by rw [hlist]; exact step_eq e1 e2⟩
  | le m n =>
      intro rest h
      obtain ⟨f1, h1⟩ := parseTerm_unparse_term m (termSafe_unparse_term n rest)
      obtain ⟨f2, h2⟩ := parseTerm_unparse_term n (formSafe_termSafe h)
      have e1 := parseTerm_mono (show f1 ≤ f1 + f2 by omega) h1
      have e2 := parseTerm_mono (show f2 ≤ f1 + f2 by omega) h2
      have hlist : unparse (Formula.le m n) ++ rest
          = L.leq :: (unparse_term m ++ (unparse_term n ++ rest)) := by simp
      exact ⟨f1 + f2 + 2, by rw [hlist]; exact step_le e1 e2⟩
  | not p ih =>
      intro rest h
      obtain ⟨f, hf⟩ := ih (L.r_par :: rest) (by simp)
      have hlist : unparse (Formula.not p) ++ rest
          = L.not :: L.l_par :: (unparse p ++ L.r_par :: rest) := by simp
      exact ⟨f + 1, by rw [hlist]; exact step_not hf⟩
  | and p q ihp ihq =>
      intro rest h
      obtain ⟨f1, h1⟩ := ihp (L.and :: (unparse q ++ L.r_par :: rest)) (by simp)
      obtain ⟨f2, h2⟩ := ihq (L.r_par :: rest) (by simp)
      have e1 := parseFormula_mono (show f1 ≤ f1 + f2 by omega) h1
      have e2 := parseFormula_mono (show f2 ≤ f1 + f2 by omega) h2
      have hlist : unparse (Formula.and p q) ++ rest
          = L.l_par :: (unparse p ++ L.and :: (unparse q ++ L.r_par :: rest)) := by simp
      exact ⟨f1 + f2 + 2, by rw [hlist]; exact step_and e1 e2⟩
  | or p q ihp ihq =>
      intro rest h
      obtain ⟨f1, h1⟩ := ihp (L.or :: (unparse q ++ L.r_par :: rest)) (by simp)
      obtain ⟨f2, h2⟩ := ihq (L.r_par :: rest) (by simp)
      have e1 := parseFormula_mono (show f1 ≤ f1 + f2 by omega) h1
      have e2 := parseFormula_mono (show f2 ≤ f1 + f2 by omega) h2
      have hlist : unparse (Formula.or p q) ++ rest
          = L.l_par :: (unparse p ++ L.or :: (unparse q ++ L.r_par :: rest)) := by simp
      exact ⟨f1 + f2 + 2, by rw [hlist]; exact step_or e1 e2⟩
  | imp p q ihp ihq =>
      intro rest h
      obtain ⟨f1, h1⟩ := ihp (L.imp :: (unparse q ++ L.r_par :: rest)) (by simp)
      obtain ⟨f2, h2⟩ := ihq (L.r_par :: rest) (by simp)
      have e1 := parseFormula_mono (show f1 ≤ f1 + f2 by omega) h1
      have e2 := parseFormula_mono (show f2 ≤ f1 + f2 by omega) h2
      have hlist : unparse (Formula.imp p q) ++ rest
          = L.l_par :: (unparse p ++ L.imp :: (unparse q ++ L.r_par :: rest)) := by simp
      exact ⟨f1 + f2 + 2, by rw [hlist]; exact step_imp e1 e2⟩
  | forall_ k p ih =>
      intro rest h
      obtain ⟨f, hf⟩ := ih (L.r_par :: rest) (by simp)
      have hlist : unparse (Formula.forall_ k p) ++ rest
          = L.all :: L.var :: (List.replicate k L.prime
              ++ L.l_par :: (unparse p ++ L.r_par :: rest)) := by simp
      exact ⟨f + 3, by rw [hlist]; exact step_forall hf⟩
  | exists_ k p ih =>
      intro rest h
      obtain ⟨f, hf⟩ := ih (L.r_par :: rest) (by simp)
      have hlist : unparse (Formula.exists_ k p) ++ rest
          = L.exi :: L.var :: (List.replicate k L.prime
              ++ L.l_par :: (unparse p ++ L.r_par :: rest)) := by simp
      exact ⟨f + 3, by rw [hlist]; exact step_exists hf⟩

theorem unparse_parse_id : ∀ φ : Formula,
    ∃ fuel, parse fuel (unparse φ) = some φ := by
  intro φ
  obtain ⟨f, hf⟩ := parseFormula_unparse φ [] (by simp)
  rw [List.append_nil] at hf
  exact ⟨f, by simp only [parse, hf]; simp⟩
