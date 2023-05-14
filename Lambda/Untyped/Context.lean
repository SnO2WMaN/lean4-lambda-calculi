abbrev Context := Array String

section Context

def pickFreshName (ctx : Context) (x : String) : Context × String :=
  match ctx.indexOf? x with
  | none => (#[x] ++ ctx, x)
  | some _ => let fn := x ++ "'"; (#[fn] ++ ctx, fn)

#eval pickFreshName #["x", "y", "z"] "x"

end Context
