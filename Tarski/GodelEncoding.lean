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
  | n + 1 => digits17Helper ((n + 1)/ 17) ++ [n % 17]
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

#eval decodeL 7

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

def diagonal_formula (fuel n : Nat) : Option Formula := do
  let φₙ ← decode fuel n
  return (.forall_ 0 (.imp (.eq (.var 0) (.var n)) φₙ))

def p : Formula := (.forall_ 0 (.imp (.eq (.var 0) (.var 1)) (.eq (.var 1) (.var 2))))

#eval (unparse p)
#eval List.map symbolCode (unparse p)
-- [15, 7, 9, 9, 7, 5 ] ++ unparse (.var n)  ++ [ 14 ] ++ unparse φₙ ++ [ 10, 10]

def diagonal (fuel n : Nat) : Option Nat := do
  let f ← diagonal_formula fuel n
  return ⌜f⌝

def diagonalR (n φ  : Nat): Prop :=
exists fuel, diagonal fuel n = some φ

end Godel
