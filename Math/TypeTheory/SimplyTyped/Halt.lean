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

def HeredHalts.weaken_at_level {level: ℕ} (term: Term) (new_ty: SimpleLamType)
  (term_wt: term.IsSimplyWellTyped ctx ty):
  term.HeredHalts term_wt ->
  (term.weaken_at_level level).HeredHalts (term_wt.weaken_at_level level new_ty) := by
  sorry

def HeredHalts.weaken (term: Term) (new_ty: SimpleLamType)
  (term_wt: term.IsSimplyWellTyped ctx ty):
  term.HeredHalts term_wt ->
  term.weaken.HeredHalts (term_wt.weaken new_ty) := by
  apply weaken_at_level

def HeredHalts.subst_at {var: ℕ} (term subst: Term)
  (hn: var < ctx.length)
  (term_wt: term.IsSimplyWellTyped ctx ty)
  (subst_wt: subst.IsSimplyWellTyped (ctx.eraseIdx var) ctx[var]):
  term.HeredHalts term_wt -> subst.HeredHalts subst_wt ->
  (term.subst subst var).HeredHalts (term_wt.subst_at hn subst_wt) := by
  sorry

def HeredHalts.subst (term subst: Term)
  (term_wt: term.IsSimplyWellTyped (arg_ty::ctx) ty)
  (subst_wt: subst.IsSimplyWellTyped ctx arg_ty):
  term.HeredHalts term_wt -> subst.HeredHalts subst_wt ->
  (term.subst subst 0).HeredHalts (term_wt.subst subst_wt) := by
  apply HeredHalts.subst_at (var := 0)
  apply Nat.zero_lt_succ

end Term
