namespace Lang

inductive Num where
  | var : Nat → Num
  | zero : Num
  | succ : Num → Num
deriving Repr

inductive Term where
  | num : Num → Term
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

@[simp]
def num_of_nat : Nat → Num
| .zero => .zero
| .succ n => .succ (num_of_nat n)

@[simp]
def term_of_nat : Nat → Term := .num ∘ num_of_nat

@[simp]
def substTerm : Term → Term → Term := fun t t' =>
  match t with
  | .num n =>
    match n with
    | .var nᵥ => if nᵥ = 0 then t' else t
    | _ => t
  | _ => t

@[simp]
def subst : Formula → Term → Formula := fun ψ t =>
  match ψ with
  | .eq t1 t2 => .eq (substTerm t1 t) (substTerm t2 t)
  | .le t1 t2 => .le (substTerm t1 t) (substTerm t2 t)
  | .and t1 t2 => .and (subst t1 t) (subst t2 t)
  | .or t1 t2 => .or (subst t1 t) (subst t2 t)
  | .imp t1 t2 => .imp (subst t1 t) (subst t2 t)
  | .not t1 => .not (subst t1 t)
  | .forall_ n p => if n = 0 then ψ else .forall_ n (subst p t)
  | .exists_ n p => if n = 0 then ψ else .exists_ n (subst p t)


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
  .forall_ 0 (.le (.num $ .var 0) (.num $ .var 0))

@[simp]
def less_then : Nat → Nat → Prop := fun m n => m ≤ n ∧ ¬ (m = n)

@[simp]
def ltFormula : Formula :=
  Formula.and
    (Formula.le (Term.num $ .var 0) (.num $ .var 1))
    (Formula.not (Formula.eq (.num $ .var 0) (.num $ .var 1)))-- Example

#eval List.replicate 1 L.prime

@[simp]
def unparse_num : Num → L_formula
  | .var n => L.var :: List.replicate n L.prime
  | .zero => [L.O]
  | .succ t => unparse_num t ++ [L.S]

@[simp]
def unparse_term : Term → L_formula
| .num n => unparse_num n
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
def parseVar : L_formula → Option (Num × L_formula)
| L.var :: xs =>
    let (n, rest) := countPrimes xs
    some (.var n, rest)
| _ => none


def parseTerm (fuel: Nat) (xs : L_formula) : Option (Term × L_formula) :=
  parseAdd fuel xs
where
  parseAtom : Nat → L_formula → Option (Term × L_formula)
  | 0, _ => none
  | _, L.O :: xs =>
      some (.num .zero, xs)
  | fuel + 1, L.l_par :: xs => do
      let (t, rest) <- parseAdd fuel xs
      match rest with
      | L.r_par :: ys => some (t, ys)
      | _ => none
  | _, xs => do
      let (n, rest) ← parseVar xs
      some (.num n, rest)

  parseSucc : Nat → L_formula → Option (Term × L_formula)
  | fuel, xs => do
      let (t, rest) <- parseAtom fuel xs
      parseSuccLoop fuel t rest

  parseSuccLoop (fuel : Nat) (t : Term) : L_formula → Option (Term × L_formula)
    | L.S :: ys =>
        match fuel with
        | 0 => none
        | fuel + 1 =>
          match t with
          | .num n => parseSuccLoop fuel (.num $ .succ n) ys
          | _ => some (t, L.S :: ys)
    | ys => some (t, ys)

  parseExp : Nat → L_formula → Option (Term × L_formula)
  | 0, _ => none
  | fuel + 1, xs => do
      let (lhs, rest) <- parseSucc fuel xs
      match rest with
      | L.exp :: ys => do
          let (rhs, zs) <- parseExp fuel ys
          some (.exp lhs rhs, zs)
      | _ =>
          some (lhs, rest)

  parseMul : Nat → L_formula → Option (Term × L_formula)
    | 0, _ => none
    | fuel, xs => do
        let (lhs, rest) <- parseExp fuel xs
        parseMulLoop fuel lhs rest

  parseMulLoop : Nat → Term → L_formula → Option (Term × L_formula)
    | 0, _, L.mult :: _ => none
    | 0, acc, ys => some (acc, ys)
    | fuel+1, acc, L.mult :: ys => do
      let (rhs, zs) <- parseExp fuel ys
      parseMulLoop fuel (.mul acc rhs) zs
    | _, acc, ys => some (acc, ys)

  parseAdd : Nat → L_formula → Option (Term × L_formula)
  | 0, _ => none
  | fuel, xs => do
      let (lhs, rest) <- parseMul fuel xs
      parseAddLoop fuel lhs rest

  parseAddLoop : Nat → Term → L_formula → Option (Term × L_formula)
    | 0, _, L.plus :: _ => none
    | 0, acc, ys => some (acc, ys)
    | fuel+1, acc, L.plus :: ys => do
      let (rhs, zs) <- parseMul fuel ys
      parseAddLoop fuel (.add acc rhs) zs
    | _, acc, ys  => some (acc, ys)


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

#eval parse 10 (unparse (.imp (.eq (.num $ .var 0) (.num $ .var 1)) (.eq (.num $ .var 1) (.num $ .var 0))))

#eval parseTerm 10 (unparse_term (.num $ .var 2))
#eval parseTerm 10 (unparse_term (.num $ .succ (.var 1)))
#eval parseTerm 10 (unparse_term (.add (.num $ .var 0) (.num $ .var 1)))
#eval parseTerm 10 (unparse_term (.mul (.num $ .succ (.var 0)) (.num $ .var 2)))
#eval parseTerm 10 (unparse_term (.exp (.num $ .var 0) (.add (.num $ .var 1) (.num $ .var 2)))) -- may not round-trip as intended



end Lang
