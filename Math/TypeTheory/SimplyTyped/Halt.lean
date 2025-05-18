import Math.TypeTheory.SimplyTyped.Defs

namespace Term

open SimpleLamType (TypeCtx)

def HeredHalts {ctx: TypeCtx} {ty: SimpleLamType} (term: Term) (wt: term.IsSimplyWellTyped ctx ty) : Prop :=
  match ty with
  | .void => False
  -- a function hereditarily halts iff it halts and for any halting input
  -- the function application also halts
  | .func arg_ty ret_ty =>
    term.Halts ∧ (
      ∀{arg: Term} (ha: arg.IsSimplyWellTyped ctx arg_ty),
        HeredHalts arg ha ->
        HeredHalts (app term arg) (by
          apply IsSimplyWellTyped.app
          assumption
          assumption)
    )

namespace HeredHalts

def reduce (r: Reduce term term') (wt: IsSimplyWellTyped ctx term ty) : HeredHalts term wt ↔ HeredHalts term' (wt.reduce r) := by
  induction ty generalizing term term' ctx with
  | void => simp [HeredHalts]
  | func arg_ty ret_ty iha ihr =>
    apply Iff.intro
    · intro ⟨h₀, h⟩
      apply And.intro
      rwa [←r.halts]
      intro arg arg_wt ha
      have r' := Reduce.app_func term term' arg r
      rw [←ihr r']
      apply h
      assumption
    · intro ⟨h₀, h⟩
      apply And.intro
      rwa [r.halts]
      intro arg arg_wt ha
      have r' := Reduce.app_func term term' arg r
      rw [ihr r']
      apply h
      assumption

def reduces_to (r: ReducesTo term term') (wt: IsSimplyWellTyped ctx term ty) : HeredHalts term wt ↔ HeredHalts term' (wt.reduces_to r) := by
  induction r with
  | refl => rfl
  | cons r rs ih =>
    rw [←ih]
    apply reduce
    assumption

end HeredHalts

def Reduce.hered_halts (r: Reduce term term') (wt: IsSimplyWellTyped ctx term ty) : HeredHalts term wt ↔ HeredHalts term' (wt.reduce r) := by
  apply HeredHalts.reduce
  assumption

def ReducesTo.hered_halts (r: ReducesTo term term') (wt: IsSimplyWellTyped ctx term ty) : HeredHalts term wt ↔ HeredHalts term' (wt.reduces_to r) := by
  apply HeredHalts.reduces_to
  assumption

end Term
