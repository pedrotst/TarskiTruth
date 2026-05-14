namespace Lang

inductive Term where
  | var : Nat → Term
  | zero : Term
  | succ : Term → Term
  | add : Term → Term → Term
  | mul : Term → Term → Term
  | exp : Term → Term → Term
deriving Repr

inductive Formula where
  | eq   : Term → Term → Formula
  | le   : Term → Term → Formula
  | not  : Formula → Formula
  | and  : Formula → Formula → Formula
  | or   : Formula → Formula → Formula
  | imp  : Formula → Formula → Formula
  | forall_ : Nat → Formula → Formula
  | exists_ : Nat → Formula → Formula
deriving Repr

def term_of_nat : Nat → Term
| .zero => .zero
| .succ n => .succ (term_of_nat n)

@[simp]
def substTerm : Term → Term → Term := fun t' t =>
  match t with
  | .var nᵥ => if nᵥ = 0 then t' else t
  | .zero => .zero
  | .succ n' => .succ (substTerm t' n')
  | .add t1 t2 => .add (substTerm t' t1) (substTerm t' t2)
  | .mul t1 t2 => .mul (substTerm t' t1) (substTerm t' t2)
  | .exp t1 t2 => .exp (substTerm t' t1) (substTerm t' t2)

@[simp]
def subst : Term → Formula → Formula := fun t ψ =>
  match ψ with
  | .eq t1 t2 => .eq (substTerm t t1) (substTerm t t2)
  | .le t1 t2 => .le (substTerm t t1) (substTerm t t2)
  | .and p q => .and (subst t p) (subst t q)
  | .or p q => .or (subst t p) (subst t q)
  | .imp p q => .imp (subst t p) (subst t q)
  | .not p => .not (subst t p)
  | .forall_ n p => if n = 0 then ψ else .forall_ n (subst t p)
  | .exists_ n p => if n = 0 then ψ else .exists_ n (subst t p)

def fv_term : Term → List Nat
  | .var v => [v]
  | .zero => []
  | .succ n => fv_term n
  | .exp n m => (fv_term n) ++ fv_term m
  | .mul n m => fv_term n ++ fv_term m
  | .add n m => fv_term n ++ fv_term m

def fv : Formula → List Nat
  | .eq t1 t2 => fv_term t1 ++ fv_term t2
  | .le t1 t2 => fv_term t1 ++ fv_term t2
  | .and t1 t2 => fv t1 ++ fv t2
  | .or t1 t2 => fv t1 ++ fv t2
  | .imp t1 t2 => fv t1 ++ fv t2
  | .not t => fv t
  | .forall_ n p => (fv p).filter (fun x => x ≠ n)
  | .exists_ n p => (fv p).filter (fun x => x ≠ n)

def closed_term (t : Term) : Prop := fv_term t = []
def closed (t : Formula) : Prop := fv t = []

def one_fv_term (t : Term) : Prop := 0 ∈ fv_term t
def one_fv (t : Formula) : Prop := 0 ∈ fv t

def only_free_var_zero (φ : Formula) : Prop :=
  ∀ n, n ∈ fv φ → n = 0

def only_free_var_zero_one (φ : Formula) : Prop :=
  ∀ n, n ∈ fv φ → (n = 0 ∨ n = 1)

theorem substTerm_not_mem_fv :
  ∀ s t, 0 ∉ fv_term t → substTerm s t = t := by
  intro s t h
  induction t with
  | var v =>
      simp [fv_term, substTerm] at h ⊢
      by_cases hv : v = 0
      · subst v
        contradiction
      · simp [hv]
  | zero =>
      simp [substTerm]
  | succ n ih =>
      simp [substTerm, ih h]
  | add t₁ t₂ ih₁ ih₂ =>
      simp [fv_term] at h
      simp [substTerm, ih₁ h.1, ih₂ h.2]
  | mul t₁ t₂ ih₁ ih₂ =>
      simp [fv_term] at h
      simp [substTerm, ih₁ h.1, ih₂ h.2]
  | exp t₁ t₂ ih₁ ih₂ =>
      simp [fv_term] at h
      simp [substTerm, ih₁ h.1, ih₂ h.2]

theorem subst_not_mem_fv :
  ∀ p t, 0 ∉ fv p → subst t p = p := by
  intro p t h
  induction p with
  | eq t₁ t₂ =>
      simp [fv] at *
      constructor
      · exact substTerm_not_mem_fv t t₁ h.1
      · exact substTerm_not_mem_fv t t₂ h.2


  | le t₁ t₂ =>
      simp [fv] at *
      constructor
      · exact substTerm_not_mem_fv t t₁ h.1
      · exact substTerm_not_mem_fv t t₂ h.2

  | and p q ihp ihq =>
      simp [fv] at h
      simp [subst, ihp h.1, ihq h.2]

  | or p q ihp ihq =>
      simp [fv] at h
      simp [subst, ihp h.1, ihq h.2]

  | imp p q ihp ihq =>
      simp [fv] at h
      simp [subst, ihp h.1, ihq h.2]

  | not p ih =>
      simp [fv] at h
      simp [subst, ih h]

  | forall_ n p ih =>
      by_cases hn : n = 0
      · simp [subst, hn]
      · simp [subst, hn]
        apply ih
        intro h0
        apply h
        simp [fv, h0]
        exact fun h0n => hn h0n.symm

  | exists_ n p ih =>
      by_cases hn : n = 0
      · simp [subst, hn]
      · simp [subst, hn]
        apply ih
        intro h0
        apply h
        simp [fv, h0]
        exact fun h0n => hn h0n.symm

theorem closed_subst :
  forall t p, closed p → subst t p = p := by
  intro t p hp
  apply subst_not_mem_fv
  intro h0
  unfold closed at hp
  rw [hp] at h0
  cases h0

inductive L where
| O
| S
| plus
| mult
| exp
| eq
| leq
| var
| prime
| l_par
| r_par
| not
| and
| or
| imp
| all
| exi
deriving Repr

instance : ToString L where
  toString
  | .O => "O"
  | .S => "S"
  | .plus => "+"
  | .mult => "x"
  | .exp => "E"
  | .eq => "="
  | .leq => "≤"
  | .var => "⋎"
  | .prime => "'"
  | .l_par => "("
  | .r_par => ")"
  | .not => "¬"
  | .and => "∧"
  | .or => "∨"
  | .imp => "→"
  | .all => "∀"
  | .exi => "∃"

instance : Repr L where
  reprPrec d _ := Std.Format.text (toString d)

abbrev L_formula := List L

-- Examples
@[simp]
def reflLe : Formula :=
  .forall_ 0 (.le (.var 0) (.var 0))

@[simp]
def less_then : Nat → Nat → Prop := fun m n => m ≤ n ∧ ¬ (m = n)

@[simp]
def ltFormula : Formula :=
  Formula.and
    (.le (.var 0) (.var 1))
    (.not (Formula.eq (.var 0) (.var 1)))-- Example

#eval List.replicate 1 L.prime

@[simp]
def unparse_term : Term → L_formula
| .var n => L.var :: List.replicate n L.prime
| .zero => [L.O]
| .succ t => unparse_term t ++ [L.S]
| .add m n => [L.l_par] ++ unparse_term m ++ [L.plus] ++ unparse_term n ++ [L.r_par]
| .mul m n => [L.l_par] ++ unparse_term m ++ [L.mult] ++ unparse_term n ++ [L.r_par]
| .exp m n => [L.l_par] ++ unparse_term m ++ [L.exp] ++ unparse_term n ++ [L.r_par]

@[simp]
def unparse : Formula → L_formula
| .eq m n        => unparse_term m ++ L.eq :: unparse_term n
| .le m n        => unparse_term m ++ L.leq :: unparse_term n
| .not p         => [L.not, L.l_par] ++ unparse p ++ [L.r_par]
| .and p q       => [L.l_par] ++ unparse p ++ [L.and] ++ unparse q ++ [L.r_par]
| .or p q        => [L.l_par] ++ unparse p ++ [L.or] ++ unparse q ++ [L.r_par]
| .imp p q       => [L.l_par] ++ unparse p ++ [L.imp] ++ unparse q ++ [L.r_par]
| .forall_ n p   => [L.all, L.var] ++ List.replicate n L.prime ++ [L.l_par] ++ unparse p ++ [L.r_par]
| .exists_ n p   => [L.exi, L.var] ++ List.replicate n L.prime ++ [L.l_par] ++ unparse p ++ [L.r_par]

-- #eval unparse ltFormula
-- #eval unparse reflLe

@[simp]
def countPrimes : L_formula → Nat × L_formula
| [] => (0, [])
| L.prime :: xs =>
    let (n, rest) := countPrimes xs
    (n + 1, rest)
| xs => (0, xs)

@[simp]
def parseVar : L_formula → Option (Term × L_formula)
  | L.var :: xs =>
      let (n, rest) := countPrimes xs
      some (.var n, rest)
  | _ => none

def parseTerm (fuel : Nat) (xs : L_formula) : Option (Term × L_formula) :=
  parseAdd fuel xs
where
  parseAtom : Nat → L_formula → Option (Term × L_formula)
    | 0, _ => none
    | _, L.O :: xs =>
        some (.zero, xs)
    | fuel + 1, L.l_par :: xs => do
        let (t, rest) ← parseAdd fuel xs
        match rest with
        | L.r_par :: ys => some (t, ys)
        | _ => none
    | _, xs => do
        parseVar xs

  parseSucc : Nat → L_formula → Option (Term × L_formula)
    | fuel, xs => do
        let (t, rest) ← parseAtom fuel xs
        parseSuccLoop fuel t rest

  parseSuccLoop : Nat → Term → L_formula → Option (Term × L_formula)
    | 0, _, L.S :: _ => none
    | 0, acc, ys => some (acc, ys)
    | fuel + 1, acc, L.S :: ys =>
        parseSuccLoop fuel (.succ acc) ys
    | _, acc, ys =>
        some (acc, ys)

  parseExp : Nat → L_formula → Option (Term × L_formula)
    | 0, _ => none
    | fuel + 1, xs => do
        let (lhs, rest) ← parseSucc fuel xs
        match rest with
        | L.exp :: ys => do
            let (rhs, zs) ← parseExp fuel ys
            some (.exp lhs rhs, zs)
        | _ =>
            some (lhs, rest)

  parseMul : Nat → L_formula → Option (Term × L_formula)
    | 0, _ => none
    | fuel, xs => do
        let (lhs, rest) ← parseExp fuel xs
        parseMulLoop fuel lhs rest

  parseMulLoop : Nat → Term → L_formula → Option (Term × L_formula)
    | 0, _, L.mult :: _ => none
    | 0, acc, ys => some (acc, ys)
    | fuel + 1, acc, L.mult :: ys => do
        let (rhs, zs) ← parseExp fuel ys
        parseMulLoop fuel (.mul acc rhs) zs
    | _, acc, ys =>
        some (acc, ys)

  parseAdd : Nat → L_formula → Option (Term × L_formula)
    | 0, _ => none
    | fuel, xs => do
        let (lhs, rest) ← parseMul fuel xs
        parseAddLoop fuel lhs rest

  parseAddLoop : Nat → Term → L_formula → Option (Term × L_formula)
    | 0, _, L.plus :: _ => none
    | 0, acc, ys => some (acc, ys)
    | fuel + 1, acc, L.plus :: ys => do
        let (rhs, zs) ← parseMul fuel ys
        parseAddLoop fuel (.add acc rhs) zs
    | _, acc, ys =>
        some (acc, ys)

#eval parseTerm 2 [L.var, L.plus, L.var]
#eval parseTerm 3 [L.l_par, L.var, L.plus, L.var, L.r_par]
#eval parseTerm 4 [L.O, L.S, L.S, L.S]


@[simp]
def parseFormula (fuel : Nat) (xs : L_formula) : Option (Formula × L_formula) :=
  parseImp fuel xs
where
  @[simp]
  parseAtomic : Nat → L_formula → Option (Formula × L_formula)
  | fuel, xs => do
      let (t1, rest1) <- parseTerm fuel xs
      match rest1 with
      | L.eq :: rest2 => do
          let (t2, rest3) <- parseTerm fuel rest2
          some (.eq t1 t2, rest3)
      | L.leq :: rest2 => do
          let (t2, rest3) <- parseTerm fuel rest2
          some (.le t1 t2, rest3)
      | _ => none

  @[simp]
  parseQuantifier : Nat → L_formula → Option (Formula × L_formula)
  | 0, _ => none
  | fuel + 1, L.all :: L.var :: xs => do
      let (n, rest1) := countPrimes xs
      match rest1 with
      | L.l_par :: rest2 => do
          let (p, rest3) <- parseImp fuel rest2
          match rest3 with
          | L.r_par :: rest4 => some (.forall_ n p, rest4)
          | _ => none
      | _ => none
  | fuel + 1, L.exi :: L.var :: xs => do
      let (n, rest1) := countPrimes xs
      match rest1 with
      | L.l_par :: rest2 => do
          let (p, rest3) <- parseImp fuel rest2
          match rest3 with
          | L.r_par :: rest4 => some (.exists_ n p, rest4)
          | _ => none
      | _ => none
  | _, _ => none

  @[simp]
  parseNot : Nat → L_formula → Option (Formula × L_formula)
  | 0, _ => none
  | fuel + 1, L.not :: L.l_par :: xs => do
      let (p, rest1) <- parseImp fuel xs
      match rest1 with
      | L.r_par :: rest2 => some (.not p, rest2)
      | _ => none
  | fuel + 1, xs =>
      parseBase fuel xs

  @[simp]
  parseBase : Nat → L_formula → Option (Formula × L_formula)
  | 0, _ => none
  | fuel + 1, L.l_par :: xs => do
      let (p, rest1) <- parseImp fuel xs
      match rest1 with
      | L.and :: rest2 => do
          let (q, rest3) <- parseImp fuel rest2
          match rest3 with
          | L.r_par :: rest4 => some (.and p q, rest4)
          | _ => none
      | L.or :: rest2 => do
          let (q, rest3) <- parseImp fuel rest2
          match rest3 with
          | L.r_par :: rest4 => some (.or p q, rest4)
          | _ => none
      | L.imp :: rest2 => do
          let (q, rest3) <- parseImp fuel rest2
          match rest3 with
          | L.r_par :: rest4 => some (.imp p q, rest4)
          | _ => none
      | L.r_par :: rest2 =>
          some (p, rest2)
      | _ => none
  | fuel + 1, xs =>
      match parseQuantifier fuel xs with
      | some res => some res
      | none =>
        match parseAtomic fuel xs with
        | some res => some res
        | none => none

  @[simp]
  parseImp : Nat → L_formula → Option (Formula × L_formula)
  | fuel, xs => parseNot fuel xs

@[simp]
def parse (fuel : Nat) (xs : L_formula) : Option Formula := do
  let (p, rest) <- parseFormula fuel xs
  if rest = [] then some p else none

#eval parse 10 (unparse reflLe)
#eval parse 10 (unparse ltFormula)

#eval parse 10 (unparse (.imp (.eq (.var 0) (.var 1)) (.eq (.var 1) (.var 0))))

#eval parseTerm 10 (unparse_term (.var 2))
#eval parseTerm 10 (unparse_term (.succ (.var 1)))
#eval parseTerm 10 (unparse_term (.add (.var 0) (.var 1)))
#eval parseTerm 10 (unparse_term (.mul (.succ (.var 0)) (.var 2)))
#eval parseTerm 10 (unparse_term (.exp (.var 0) (.add (.var 1) (.var 2)))) -- may not round-trip as intended



end Lang
