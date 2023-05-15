namespace Nat

def subDigitChar (n : Nat) : Char :=
  if n = 0 then '₀' else
  if n = 1 then '₁' else
  if n = 2 then '₂' else
  if n = 3 then '₃' else
  if n = 4 then '₄' else
  if n = 5 then '₅' else
  if n = 6 then '₆' else
  if n = 7 then '₇' else
  if n = 8 then '₈' else
  if n = 9 then '₉' else
  '*'

partial def toSubDigitsAux : Nat → List Char → List Char
  | n, ds =>
    let d  := subDigitChar <| n % 10;
    let n' := n / 10;
    if n' = 0 then d::ds
    else toSubDigitsAux n' (d::ds)

def toSubDigits (n : Nat) : List Char :=
  toSubDigitsAux n []

def toSubscriptString (n : Nat) : String :=
  (toSubDigits n).asString

end Nat

abbrev Context := Array String

section Context

def pickFreshName (ctx : Context) : Context × String :=
  let n := "v" ++ ctx.size.toSubscriptString
  (#[n] ++ ctx, n)

#check Repr
#eval pickFreshName #[]
#eval pickFreshName #["x"]

end Context

inductive Term
  | Var : Nat → Term
  | Abs : Term → Term
  | App : Term → Term → Term

section Term

open Term

def toString : Term → String
  | Var k => s!"{k}"
  | Abs t => "(λ." ++ toString t ++ ")"
  | App t₁ t₂ => "(" ++ toString t₁ ++ " " ++ toString t₂ ++ ")"

instance : ToString Term := ⟨toString⟩

def isValue : Term → Bool
  | .Var _ => true
  | Abs _ => true
  | _ => false

def shift (c d : Nat) (t : Term) : Term :=
  match t with
  | Var k => if k < c then Var k else Var (k + d)
  | Abs t => Abs (shift (c + 1) d t)
  | App t₁ t₂ => App (shift c d t₁) (shift c d t₂)

def shift0 := shift 0

#eval (shift0 1 (Var 1))
#eval (shift0 1 (shift0 1 (Var 1)))

def subst (j : Nat) (s : Term) (t : Term) :=
  match t with
  | Var k => if k == j then s else Var k
  | Abs t => Abs (subst (j + 1) (shift0 1 s) t)
  | App t₁ t₂ => App (subst j s t₁) (subst j s t₂)

#eval (subst 0 (Var 1) (App (Var 0) (Abs (Abs (App (Var 0) (Var 2))))))

def print (ctx : Context) : Term → Option String
  | Var k => ctx.get? k
  | Abs t => do
    let (ctx', x') := pickFreshName ctx
    let s <- print ctx' t
    return "(λ" ++ x' ++ "." ++ s ++ ")"
  | App t₁ t₂ => do
    let s₁ <- print ctx t₁
    let s₂ <- print ctx t₂
    return "(" ++ s₁ ++ " " ++ s₂ ++ ")"

#eval print #["x", "y"] (App (Var 1) (Abs  (Abs (App (Var 0) (Var 3)))))
#eval print #["x", "y"] (subst 0 (Var 1) (App (Var 0) (Abs  (Abs (App (Var 0) (Var 2))))))
#eval (print #["x", "y"] (App (Var 1) (Abs  (Abs (App (Var 0) (Var 3)))))) == (print #["x", "y"] (subst 0 (Var 1) (App (Var 0) (Abs  (Abs (App (Var 0) (Var 2)))))))

#eval App (App (Abs  (Abs (App (Var 0) (Var 1)))) (Var 0)) (Abs  (Var 0))
#eval print #["z"] (App (App (Abs  (Abs (App (Var 0) (Var 1)))) (Var 0)) (Abs  (Var 0)))

end Term

namespace Smallstep

open Term

def simpl1 : Term → Option Term
  | App (Abs t) t₂ => if isValue t₂ then some (subst 0 t₂ t) else none
  | App t₁ t₂ => match simpl1 t₁ with
    | some t₁' => some (App t₁' t₂)
    | none => match simpl1 t₂ with
      | some t₂' => some (App t₁ t₂')
      | _ => none
  | _ => none

def simpl (t : Term) : Term :=
  match simpl1 t with
  | some t' => simpl t'
  | none => t

#eval print #["z"] (App (Abs (Abs (App (Var 0) (Var 1)))) (Var 0))
#eval simpl (App (Abs  (Abs (App (Var 0) (Var 1)))) (Var 0))
#eval print #["z"] (simpl (App (Abs (Abs (App (Var 0) (Var 1)))) (Var 0)))

#eval simpl (App (App (Abs (Abs (App (Var 0) (Var 1)))) (Var 0)) (Abs (Var 0)))

#eval print #["z"] (simpl (App (App (Abs (Abs (App (Var 0) (Var 1)))) (Var 0)) (Abs  (Var 0))))

end Smallstep
