import Math.TypeTheory.SimplyTyped.Defs

namespace Term

open SimpleLamType (TypeCtx)

def HeredHalts {ty: SimpleLamType} (term: Term) (wt: term.IsSimplyWellTyped [] ty) : Prop :=
  match ty with
  | .void => False
  -- a function hereditarily halts iff it halts and for any halting input
  -- the function application also halts
  | .func arg_ty ret_ty =>
    term.Halts ∧ (
      ∀{arg: Term} (ha: arg.IsSimplyWellTyped [] arg_ty),
        HeredHalts arg ha ->
        HeredHalts (app term arg) (by
          apply IsSimplyWellTyped.app
          assumption
          assumption)
    )

namespace HeredHalts

def Halts {term: Term} {wt: term.IsSimplyWellTyped [] ty} (h: term.HeredHalts wt) : term.Halts := by
  cases ty
  contradiction
  exact h.left

def reduce (r: Reduce term term') (wt: IsSimplyWellTyped [] term ty) : HeredHalts term wt ↔ HeredHalts term' (wt.reduce r) := by
  induction ty generalizing term term' with
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

def reduces_to (r: ReducesTo term term') (wt: IsSimplyWellTyped [] term ty) : HeredHalts term wt ↔ HeredHalts term' (wt.reduces_to r) := by
  induction r with
  | refl => rfl
  | cons r rs ih =>
    rw [←ih]
    apply reduce
    assumption

end HeredHalts

def Reduce.hered_halts (r: Reduce term term') (wt: IsSimplyWellTyped [] term ty) : HeredHalts term wt ↔ HeredHalts term' (wt.reduce r) := by
  apply HeredHalts.reduce
  assumption

def ReducesTo.hered_halts (r: ReducesTo term term') (wt: IsSimplyWellTyped [] term ty) : HeredHalts term wt ↔ HeredHalts term' (wt.reduces_to r) := by
  apply HeredHalts.reduces_to
  assumption

inductive HeredHalts.SubstAll : TypeCtx -> List Term -> Prop where
| nil : SubstAll [] []
| cons (wt: term.IsSimplyWellTyped [] ty) :
  term.HeredHalts wt ->
  SubstAll ctx terms ->
  SubstAll (ty::ctx) (term::terms)

protected def HeredHalts.SubstAll.well_typed (h: HeredHalts.SubstAll ctx terms) : IsSimplyWellTyped.SubstAll ctx terms := by
  induction h with
  | nil => apply IsSimplyWellTyped.SubstAll.nil
  | cons => apply IsSimplyWellTyped.SubstAll.cons <;> assumption

protected def HeredHalts.SubstAll.HeredHalts (h: HeredHalts.SubstAll ctx terms) (hi: i < terms.length) : terms[i].HeredHalts (h.well_typed.wt hi) := by
  induction h generalizing i with
  | nil => contradiction
  | cons _ _ _ ih =>
    cases i
    assumption
    apply ih

def HeredHalts.subst_all
  (term: Term) (substs: List Term)
  (h: HeredHalts.SubstAll ctx substs)
  (wt: term.IsSimplyWellTyped ctx ty) :
  (term.subst_all 0 substs).HeredHalts (by
    apply IsSimplyWellTyped.subst_all (ctx₀ := [])
    simp
    assumption
    apply h.well_typed) := by
  induction wt generalizing substs with
  | app ctx func arg arg_ty ret_ty func_wt arg_wt ihf iha =>
    conv => { lhs; rw [susbt_all_app (h := h.well_typed)] }
    apply (ihf _ _).right
    apply iha
    assumption
    assumption
  | var _ name ty =>
    conv => {
      lhs; rw [subst_all_var_of_ge (h := h.well_typed) (hname := by
        rwa [←h.well_typed.length_eq]) (hname' := by
        apply Nat.zero_le)]
    }
    subst ty
    apply h.HeredHalts (i := name)
  | lam ctx body arg_ty ret_ty wt ih =>
    apply And.intro
    exists (body.subst_all 1 substs).lam
    apply And.intro
    apply IsValue.lam
    rw [susbt_all_lam]
    apply h.well_typed
    intro arg arg_wt ha
    conv => { lhs; rw [susbt_all_lam (h := h.well_typed)] }
    obtain ⟨a', a'_val, red⟩ := ha.Halts
    apply (HeredHalts.reduces_to (term' := (body.subst_all 1 substs).lam.app a') _ _).mpr
    apply (HeredHalts.reduce (term' := (body.subst_all 1 substs).subst a' 0) _ _).mpr
    · suffices (body.subst_all (0 + 1) substs).subst a' 0 = body.subst_all 0 (a'::substs) by
        conv => {
          lhs; rw [this]
        }
        apply ih
        apply SubstAll.cons
        apply (HeredHalts.reduces_to red _).mp
        assumption
        assumption
      · apply subst_all_subst_succ (ctx₀ := []) (subst_ty := arg_ty) (ctx' := ctx)
        simpa
        apply IsSimplyWellTyped.SubstAll.cons
        apply IsSimplyWellTyped.reduces_to
        assumption
        assumption
        apply h.well_typed
    · simp
      clear ha arg_wt
      induction red with
      | refl => rfl
      | cons _ _ ih =>
        apply Relation.ReflTransGen.cons
        apply Reduce.app_arg
        apply IsValue.lam
        assumption
        apply ih
        assumption
    · apply Reduce.apply
      assumption

-- every term which is well typed in the empty context eventually halts!
protected def IsSimplyWellTyped.Halts {term: Term} (wt: term.IsSimplyWellTyped [] ty) : term.Halts :=
  (HeredHalts.subst_all term [] .nil wt).Halts

end Term

structure SimplyWellTypedTerm (ty: SimpleLamType) where
  term: Term
  prf: term.IsSimplyWellTyped [] ty

instance : WellFoundedRelation (SimplyWellTypedTerm ty) where
  rel a b := Term.Reduce b.term a.term
  wf := by
    apply WellFounded.intro
    intro ⟨a, ha⟩
    have ⟨val, hval, red⟩ := ha.Halts
    induction red with
    | refl =>
      apply Acc.intro
      intro y red
      have := hval.notReduce _ red
      contradiction
    | @cons term₀ term₁ term₂ red₀₁ red₁₂ ih =>
      have := ih (by
        apply Term.IsSimplyWellTyped.reduce
        assumption
        assumption) hval
      apply Acc.intro
      intro ⟨y, hy⟩ h
      simp at h
      have := red₀₁.unique h
      subst y
      assumption

namespace SimplyWellTypedTerm

-- evaluate a term which is simply well typed in the empty context to a value of the same type
def eval (term: SimplyWellTypedTerm ty) : SimplyWellTypedTerm ty :=
  match term.term.findReduction with
  | .inl ⟨b, hb⟩ =>
    eval {
      term := b
      prf := by
        apply Term.IsSimplyWellTyped.reduce
        exact term.prf
        assumption
    }
  | .inr no_red => term
termination_by term

def eval_is_value (term: SimplyWellTypedTerm ty) : term.eval.term.IsValue := by
  induction term using eval.induct with
  | case1 x b h g ih =>
    unfold eval
    rwa [g]
  | case2 x h g =>
    unfold eval
    rw [g]
    dsimp
    apply (Term.reduce_or_value x.term x.prf).resolve_right
    assumption

def eval_reduces_to (term: SimplyWellTypedTerm ty) : Term.ReducesTo term.term term.eval.term := by
  induction term using eval.induct with
  | case1 x b h g ih =>
    unfold eval
    rw [g]
    apply Relation.ReflTransGen.cons <;> assumption
  | case2 x h g =>
    unfold eval
    rw [g]

end SimplyWellTypedTerm
