abbrev Context := Array String

section Context

def pickFreshName (ctx : Context) (x : String) : Context × String :=
  match ctx.indexOf? x with
  | none => (#[x] ++ ctx, x)
  | some _ => let fn := x ++ "'"; (#[fn] ++ ctx, fn)

#eval pickFreshName #[] "x"
#eval pickFreshName #["x"] "x"

end Context

inductive Term
  | Var : Nat → Term
  | Abs : String → Term → Term
  | App : Term → Term → Term

section Term

open Term

def toString : Term → String
  | Var k => s!"{k}"
  | Abs _ t => "(λ." ++ toString t ++ ")"
  | App t₁ t₂ => "(" ++ toString t₁ ++ " " ++ toString t₂ ++ ")"

instance : ToString Term := ⟨toString⟩

def isValue : Term → Bool
  | .Var _ => true
  | Abs _ _ => true
  | _ => false

def shift (c d : Nat) (t : Term) : Term :=
  match t with
  | Var k => if k < c then Var k else Var (k + d)
  | Abs x t => Abs x (shift (c + 1) d t)
  | App t₁ t₂ => App (shift c d t₁) (shift c d t₂)

def shift0 := shift 0

#eval (shift0 1 (Var 1))
#eval (shift0 1 (shift0 1 (Var 1)))

def subst (j : Nat) (s : Term) (t : Term) :=
  match t with
  | Var k => if k == j then s else Var k
  | Abs x t => Abs x (subst (j + 1) (shift0 1 s) t)
  | App t₁ t₂ => App (subst j s t₁) (subst j s t₂)

#eval (subst 0 (Var 1) (App (Var 0) (Abs "α" (Abs "β" (App (Var 0) (Var 2))))))

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

#eval print #["x", "y"] (App (Var 1) (Abs "α" (Abs "β" (App (Var 0) (Var 3)))))
#eval print #["x", "y"] (subst 0 (Var 1) (App (Var 0) (Abs "α" (Abs "β" (App (Var 0) (Var 2))))))
#eval (print #["x", "y"] (App (Var 1) (Abs "α" (Abs "β" (App (Var 0) (Var 3)))))) == (print #["x", "y"] (subst 0 (Var 1) (App (Var 0) (Abs "α" (Abs "β" (App (Var 0) (Var 2)))))))

#eval App (App (Abs "α" (Abs "β" (App (Var 0) (Var 1)))) (Var 0)) (Abs "α" (Var 0))
#eval print #["z"] (App (App (Abs "α" (Abs "β" (App (Var 0) (Var 1)))) (Var 0)) (Abs "α" (Var 0)))

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

#eval print #["z"] (App (Abs "α" (Abs "β" (App (Var 0) (Var 1)))) (Var 0))
#eval simpl (App (Abs "α" (Abs "β" (App (Var 0) (Var 1)))) (Var 0))
#eval print #["z"] (simpl (App (Abs "α" (Abs "β" (App (Var 0) (Var 1)))) (Var 0)))

#eval simpl (App (App (Abs "α" (Abs "β" (App (Var 0) (Var 1)))) (Var 0)) (Abs "α" (Var 0)))

#eval print #["z"] (simpl (App (App (Abs "α" (Abs "β" (App (Var 0) (Var 1)))) (Var 0)) (Abs "α" (Var 0))))

end Smallstep
