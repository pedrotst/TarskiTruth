import Tarski.Lang

namespace Godel
open Lang

@[simp]
def symbolCode : L → Nat
| .O      => 1
| .S      => 0
| .plus   => 2
| .mult   => 3
| .exp    => 4
| .eq     => 5
| .leq    => 6
| .var    => 7
| .prime  => 8
| .l_par  => 9
| .r_par  => 10
| .not    => 11
| .and    => 12
| .or     => 13
| .imp    => 14
| .all    => 15
| .exi    => 16

@[simp]
def codeSymbol : Nat → Option L
| 1  => some .O
| 0  => some .S
| 2  => some .plus
| 3  => some .mult
| 4  => some .exp
| 5  => some .eq
| 6  => some .leq
| 7  => some .var
| 8  => some .prime
| 9  => some .l_par
| 10 => some .r_par
| 11 => some .not
| 12 => some .and
| 13 => some .or
| 14 => some .imp
| 15 => some .all
| 16 => some .exi
| _  => none

@[simp]
def encodeL : L_formula → Nat :=
  List.foldl (fun acc sym => acc * 17 + symbolCode sym) 0

#eval encodeL [.O, .S, .S, .S]

def digits17Helper : Nat → List Nat
  | 0 => []
  | n + 1 => digits17Helper ((n + 1)/ 17) ++ [(n + 1) % 17]
termination_by n => n
decreasing_by
simp
grind

@[simp]
def digits17L : Nat → List Nat
  | 0 => [0]
  | n => digits17Helper n

#eval digits17L 0
#eval digits17Helper 17
#eval digits17L 39

@[simp]
def decodeDigitsL : List Nat → Option L_formula
| [] => some []
| d :: ds => do
    let s <- codeSymbol d
    let rest <- decodeDigitsL ds
    pure (s :: rest)

#eval List.map symbolCode [.O, .S, .S, .S]
#eval decodeDigitsL [0, 1]

@[simp]
def decodeL : Nat → Option L_formula := fun n =>
  decodeDigitsL (digits17L n)

#eval decodeL 19

@[simp]
def showFormula (xs : L_formula) : String :=
  String.join (xs.map toString)


@[simp]
def encode (φ : Formula) : Nat :=
  encodeL (unparse φ)

notation "⌜" φ "⌝" => encode φ

@[simp]
def decode (fuel n : Nat) : Option Formula :=
  match decodeL n with
  | some xs =>
      match parse fuel xs with
      | some φ => some φ
      | _ => none
  | none => none

def diagAt (n : Nat) (φ : Formula) : Formula :=
  .forall_ 0 (.imp (.eq (.var 0) (term_of_nat n)) φ)

def diagSentence (φ : Formula) : Formula :=
  diagAt (encode φ) φ

def p : Formula := (.forall_ 0 (.imp (.eq (.var 0) (.var 1)) (.eq (.var 1) (.var 2))))

#eval (unparse p)
#eval List.map symbolCode (unparse p)

/-!
### The diagonal relation

For a *canonical* code `n = ⌜φ⌝` with `k = (unparse φ).length`, the string

    unparse (diagAt n φ)
      = [∀,⋎,(,(,=,⋎,O] ++ replicate n S ++ [→] ++ unparse φ ++ [),)]

has base-17 code

    ((((C * 17^n) * 17 + 14) * 17^k + n) * 17 + 10) * 17 + 10

where `C = encodeL [∀,⋎,(,(,=,⋎,O] = 372800005` (the `Sⁿ` block contributes
nothing but a shift, because `symbolCode S = 0`).

`diagonalR` is defined directly by that polynomial, with `k` pinned down as the
base-17 digit length of `n` (`17^(k-1) ≤ n < 17^k`).  This is arithmetic
essentially by inspection, unlike the decode-based definition which would need a
full arithmetization of the parser.  See `PLAN.md`.
-/

/-- `C = encodeL [L.all, L.var, L.l_par, L.l_par, L.eq, L.var, L.O]`. -/
def diagC : Nat := 372800005

def diagF (n k : Nat) : Nat :=
  ((((diagC * 17 ^ n) * 17 + 14) * 17 ^ k + n) * 17 + 10) * 17 + 10

/-- `k` is the base-17 digit length of `n`. -/
def isDigitLen17 (n k : Nat) : Prop := n < 17 ^ k ∧ 17 ^ k ≤ 17 * n

def diagonalR (n m : Nat) : Prop :=
  ∃ k, isDigitLen17 n k ∧ m = diagF n k

end Godel
