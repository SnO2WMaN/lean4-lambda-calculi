abbrev Context := Array String

section Context

def pickFreshName (ctx : Context) (x : String) : Context × String :=
  match ctx.indexOf? x with
  | none => (#[x] ++ ctx, x)
  | some _ => let fn := x ++ "'"; (#[fn] ++ ctx, fn)

#eval pickFreshName #["x", "y", "z"] "x"

end Context

inductive Term
  | Var : Nat → Term
  | Abs : String → Term → Term
  | App : Term → Term → Term

section Term

open Term

def toString : Term → String
  | Var k => s!"{k}"
  | Abs x t => "λ" ++ x ++ "." ++ toString t
  | App t₁ t₂ => "(" ++ toString t₁ ++ " " ++ toString t₂ ++ ")"

instance : ToString Term := ⟨toString⟩

def isValue : Term → Bool
  | Abs _ _ => true
  | _ => false

def print (ctx : Context) : Term → Option String
  | Var k => ctx.get? k
  | Abs x t => do
    let (ctx', x') := pickFreshName ctx x
    let s <- print ctx' t
    return "(λ" ++ x' ++ "." ++ s ++ ")"
  | App t₁ t₂ => do
    let s₁ <- print ctx t₁
    let s₂ <- print ctx t₂
    return "(" ++ s₁ ++ " " ++ s₂ ++ ")"

def shift (c d : Nat) (t : Term) : Term :=
  match t with
  | Var k => if k < c then Var k else Var (k + d)
  | Abs x t => Abs x (shift (c + 1) d t)
  | App t₁ t₂ => App (shift c d t₁) (shift c d t₂)

def shift0 := shift 0

#eval (shift0 2 (App (Var 0) (Abs "a" (Abs "b" (App (Var 0) (Var 2))))))

def subst (j : Nat) (s : Term) (t : Term) :=
  match t with
  | Var k => if k == j then s else Var k
  | Abs x t => Abs x (subst (j + 1) (shift0 1 s) t)
  | App t₁ t₂ => App (subst j s t₁) (subst j s t₂)


#eval print #["a", "b"] (App (Var 0) (Abs "a" (Abs "b" (App (Var 0) (Var 2)))))
#eval print #["a", "b"] (subst 0 (Var 1) (App (Var 0) (Abs "a" (Abs "b" (App (Var 0) (Var 2))))))

end Term

namespace Smallstep

open Term

def simpl1 : Term → Option Term
  | App (Abs _ t) t₂ => if isValue t₂ then some (subst 0 t₂ t) else none
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

#eval print #[] (App (Abs "x" (Var 0)) (Abs "x" (Var 0)))
#eval print #[] (simpl (App (Abs "x" (Var 0)) (Abs "x" (Var 0))))
#eval print #["a"] (App (Abs "x" (Var 1)) (Abs "x" (Var 0)))
#eval print #["a"] (simpl (App (Abs "x" (Var 1)) (Abs "x" (Var 0))))

end Smallstep
