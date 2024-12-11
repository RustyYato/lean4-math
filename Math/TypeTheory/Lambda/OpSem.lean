import Math.TypeTheory.Lambda.Basic
import Math.Relation.Basic

namespace LamTerm

inductive Reduce : LamTerm -> LamTerm -> Prop where
| PanicBody (body body': LamTerm) (ty: LamType) : Reduce body body' -> Reduce (.Panic body ty) (.Panic body' ty)
| AppFunc (f f' arg: LamTerm) : Reduce f f' -> Reduce (.App f arg) (.App f' arg)
| AppArg (f arg arg': LamTerm) : f.IsValue -> Reduce arg arg' -> Reduce (.App f arg) (.App f arg')
| Apply (arg_ty: LamType) (body arg: LamTerm) : arg.IsValue -> Reduce (.App (.Lambda arg_ty body) arg) (body.subst arg)

infix:100 " ~> " => Reduce
infix:100 " ~*> " => Relation.ReflTransGen (· ~> ·)

def Reduce.not_value {a b: LamTerm} : a ~> b -> ¬a.IsValue := by
  intro ab h
  cases ab <;> contradiction

def Reduce.decide {a b b': LamTerm} : a ~> b -> a ~> b' -> b = b' := by
  intro ab ab'
  induction ab generalizing b' with
  | PanicBody _ _ _ _ ih =>
    cases ab'
    congr
    apply ih
    assumption
  | AppFunc _ _ _ fred ih =>
    cases ab'
    congr
    apply ih
    assumption
    have := fred.not_value
    contradiction
    have := fred.not_value
    contradiction
  | AppArg _ _ _ _ _ ih =>
    cases ab'
    rename_i fred
    have := fred.not_value
    contradiction
    congr
    apply ih
    assumption
    rename _ ~> _ => ared
    have := ared.not_value
    contradiction
  | Apply =>
    cases ab'
    rename _ ~> _ => ared
    have := ared.not_value
    contradiction
    rename _ ~> _ => ared
    have := ared.not_value
    contradiction
    rfl

def Reduction.push {a b c: LamTerm} :
  a ~> b -> b ~*> c -> a ~*> c := (Relation.ReflTransGen.trans <| Relation.ReflTransGen.single ·)

def Reduction.pop {a b c: LamTerm} (h: c.IsValue) :
  b ~> a -> b ~*> c -> a ~*> c := by
  intro ba bc
  cases bc
  have := ba.not_value
  contradiction
  rename_i bc _
  cases ba.decide bc
  assumption

def IsWellTyped.Reduce (red: a ~> b) : ∀ctx ty, a.IsWellTyped ctx ty -> b.IsWellTyped ctx ty := by
  induction red with
  | PanicBody _ _ _ _ ih =>
    intro ctx ty
    intro (.Panic _ _ _)
    apply IsWellTyped.Panic
    apply ih
    assumption
  | AppFunc _ _ _ _ ih =>
    intro ctx ty
    intro (.App _ _ _ _ _ _)
    apply IsWellTyped.App
    apply ih
    assumption
    assumption
  | AppArg _ _ _ _ _ ih =>
    intro ctx ty
    intro (.App _ _ _ _ _ _)
    apply IsWellTyped.App
    assumption
    apply ih
    assumption
  | Apply =>
    intro ctx ty
    intro (.App _ _ _ _ (.Lambda _ _ _ _) _)
    apply IsWellTyped.subst
    assumption
    assumption

def IsWellTyped.Reduction (red: a ~*> b) : ∀ctx ty, a.IsWellTyped ctx ty -> b.IsWellTyped ctx ty := by
  induction red with
  | refl => intros; assumption
  | cons _ _ ih =>
    intro ctx ty wt
    apply ih
    apply Reduce
    assumption
    assumption

inductive Halts (a: LamTerm) : Prop where
| intro (value: LamTerm) : value.IsValue -> a ~*> value -> Halts a

def Halts.Reduce (a: LamTerm) (h: a ~> b) : Halts a ↔ Halts b := by
  apply Iff.intro
  intro ⟨val, val_spec, red⟩
  refine ⟨val, val_spec, ?_⟩
  apply Reduction.pop
  assumption
  assumption
  assumption
  intro ⟨val, val_spec, red⟩
  refine ⟨val, val_spec, ?_⟩
  apply Reduction.push
  assumption
  assumption

def Halts.Reduction (a: LamTerm) (h: a ~*> b) : Halts a ↔ Halts b := by
  induction h with
  | refl => apply Iff.refl
  | cons r _ ih =>
    apply Iff.trans _ ih
    apply Halts.Reduce
    assumption

def HeredHalts {ctx ty} (a: LamTerm) (wt: a.IsWellTyped ctx ty) : Prop :=
  match ty with
  | .Void => False
  | .Unit => a.Halts
  | .Func arg_ty ret_ty =>
    a.Halts ∧ (
      ∀(arg: LamTerm) (h: arg.IsWellTyped ctx arg_ty), HeredHalts _ (.App arg_ty ret_ty a arg wt h)
    )

def Reduce.hered_halts_iff {a: LamTerm} (wt: a.IsWellTyped ctx ty) (red: a ~> b) :
  a.HeredHalts wt ↔ b.HeredHalts (wt.Reduce red) := by
  induction ty generalizing ctx a b with
  | Void => apply Iff.intro <;> (intro; contradiction)
  | Unit =>
    apply Halts.Reduce
    assumption
  | Func arg_ty ret_ty arg_ih ret_ih =>
    apply Iff.intro
    intro ⟨halts, hered⟩
    apply And.intro
    apply (Halts.Reduce _ _).mp <;> assumption
    intro arg arg_wt
    apply (ret_ih _ _).mp
    apply hered
    assumption
    apply Reduce.AppFunc
    assumption
    intro ⟨halts, hered⟩
    apply And.intro
    apply (Halts.Reduce _ _).mpr <;> assumption
    intro arg arg_wt
    apply (ret_ih _ _).mpr
    apply hered
    assumption
    apply Reduce.AppFunc
    assumption

def Reduction.hered_halts_iff {a: LamTerm} (wt: a.IsWellTyped ctx ty) (red: a ~*> b) :
  a.HeredHalts wt ↔ b.HeredHalts (wt.Reduction red) := by
  induction red generalizing ctx ty with
  | refl => apply Iff.refl
  | cons r _ ih =>
    apply Iff.trans _ (ih _)
    apply IsWellTyped.Reduce
    assumption
    assumption
    apply Reduce.hered_halts_iff
    assumption

end LamTerm
