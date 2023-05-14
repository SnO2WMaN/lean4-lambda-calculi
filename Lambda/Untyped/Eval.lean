import Lambda.Untyped.Syntax

open Term

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
