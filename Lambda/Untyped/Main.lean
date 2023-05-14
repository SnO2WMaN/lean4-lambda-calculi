inductive Term
  | var : Nat → Term
  | abs : String → Term → Term
  | app : Term → Term → Term

open Term

abbrev Context := Array String

def Context.empty : Context := #[]

def Context.pickFreshName (ctx : Context) (x : String) : Context × String :=
  match ctx.indexOf? x with
  | none => (#[x] ++ ctx, x)
  | some _ => let fn := x ++ "'"; (#[fn] ++ ctx, fn)

#eval Context.pickFreshName #["x", "y", "z"] "x"

def Term.print (ctx : Context) : Term → Option String
  | var k => ctx.get? k
  | abs x t => do
    let (ctx', x') := Context.pickFreshName ctx x
    let s <- print ctx' t
    return "(λ" ++ x' ++ "." ++ s ++ ")"
  | app t₁ t₂ => do
    let s₁ <- print ctx t₁
    let s₂ <- print ctx t₂
    return "(" ++ s₁ ++ " " ++ s₂ ++ ")"

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


def isValue : Term → Bool
  | abs _ _ => true
  | _ => false

def eval1 : Term → Option Term
  | app (abs _ t) t₂ => if isValue t₂ then some (subst 0 t₂ t) else none
  | app t₁ t₂ => match eval1 t₁ with
    | some t₁' => some (app t₁' t₂)
    | none => match eval1 t₂ with
      | some t₂' => some (app t₁ t₂')
      | _ => none
  | _ => none

def eval (t : Term) : Term :=
  match eval1 t with
  | some t' => eval t'
  | none => t

#eval print #["a", "b"] (eval (app (abs "x" (var 0)) (abs "x" (var 0))))
