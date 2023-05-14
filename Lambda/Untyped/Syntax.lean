import Lambda.Untyped.Context

inductive Term
  | var : Nat → Term
  | abs : String → Term → Term
  | app : Term → Term → Term

section Term

def Term.print (ctx : Context) : Term → Option String
  | var k => ctx.get? k
  | abs x t => do
    let (ctx', x') := pickFreshName ctx x
    let s <- print ctx' t
    return "(λ" ++ x' ++ "." ++ s ++ ")"
  | app t₁ t₂ => do
    let s₁ <- print ctx t₁
    let s₂ <- print ctx t₂
    return "(" ++ s₁ ++ " " ++ s₂ ++ ")"

end Term

open Term

def shift (c d : Nat) (t : Term) :=
  match t with
  | var k => if k < c then var k else var (k + d)
  | abs x t => abs x (shift (c + 1) d t)
  | app t₁ t₂ => app (shift c d t₁) (shift c d t₂)

def shift0 := shift 0

def subst (j : Nat) (s : Term) (t : Term) :=
  match t with
  | var k => if k == j then s else var k
  | abs x t => abs x (subst (j + 1) (shift0 1 s) t)
  | app t₁ t₂ => app (subst j s t₁) (subst j s t₂)

#eval print #["a", "b"] (app (var 0) (abs "a" (abs "b" (app (var 0) (var 2)))))
#eval print #["a", "b"] (subst 0 (var 1) (app (var 0) (abs "a" (abs "b" (app (var 0) (var 2))))))
