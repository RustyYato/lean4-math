import Math.TypeTheory.Lambda.Defs

namespace Term

inductive ReduceTo (ctx: Map Name LamType) : Term -> Term -> Prop where
| Subst :
  IsValue arg ->
  -- ensure that the relabelling is well typed
  (∀x ∈ ctx, f x = x) ->
  -- ensure that substitution is well typed
  (∀n, body.Introduces n -> (arg.relabel f).Introduces n -> False) ->
  ReduceTo ctx (.App (.Lambda argty name body) arg)
    (body.subst (arg.relabel f) name)
| Panic : ReduceTo ctx body body' -> ReduceTo ctx (.Panic body ty) (.Panic body' ty)
| AppFunc : ReduceTo ctx func func' -> ReduceTo ctx (.App func arg) (.App func' arg)
| AppArg : IsValue func -> ReduceTo ctx arg arg' -> ReduceTo ctx (.App func arg) (.App func arg')

abbrev NormalizeTo (ctx: Map Name LamType) := Relation.ReflTransGen (ReduceTo ctx)

def ReduceTo.not_value {a b: Term} : ReduceTo ctx a b -> ¬a.IsValue := by
  intro ab h
  cases ab <;> contradiction

def ReduceTo.decide {a b b': Term} : ReduceTo ctx a b -> ReduceTo ctx a b' -> b ≈ b' := by
  intro ab ab'
  induction ab generalizing b' <;> cases ab'
  rfl
  any_goals
    rename_i h
    have := h.not_value
    contradiction
  congr
  rename_i ih _ _ ; apply ih
  assumption
  rename_i h _ _
  have := h.not_value
  contradiction
  congr
  rename_i ih _ _
  apply ih
  assumption
  rename_i h _ _ _ _
  have := h.not_value
  contradiction
  rename ReduceTo _ _ _ => h
  have := h.not_value
  contradiction
  congr
  rename_i ih _ _ _
  apply ih
  assumption


end Term
