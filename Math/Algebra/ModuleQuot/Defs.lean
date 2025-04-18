import Math.Algebra.Module.Con
import Math.Algebra.Group.Con

def ModuleQuot.Con (R : Type*) [Add α] [SMul R α] (r: α -> α -> Prop) : LinearCon R α := LinearCon.generate R r

def ModuleQuot (R: Type*) [Add α] [SMul R α] (r: α -> α -> Prop) := AlgQuotient (ModuleQuot.Con R r)

namespace ModuleQuot

variable {r: M -> M -> Prop} [SMul R M]

section

instance instAddMonoidOps [AddMonoidOps M] [IsAddMonoid M] : AddMonoidOps (ModuleQuot R r) :=
  inferInstanceAs (AddMonoidOps (AlgQuotient (ModuleQuot.Con R r)))
instance instIsSemiring [AddMonoidOps M] [IsAddMonoid M] : IsAddMonoid (ModuleQuot R r) :=
  inferInstanceAs (IsAddMonoid (AlgQuotient (ModuleQuot.Con R r)))

instance instGroupOps [AddGroupOps M] [IsAddGroup M] : AddGroupOps (ModuleQuot R r) :=
  inferInstanceAs (AddGroupOps (AlgQuotient (ModuleQuot.Con R r)))
instance instIsGroup [AddGroupOps M] [IsAddGroup M] : IsAddGroup (ModuleQuot R r) :=
  inferInstanceAs (IsAddGroup (AlgQuotient (ModuleQuot.Con R r)))

instance instSMul [Add M] : SMul R (ModuleQuot R r) :=
  inferInstanceAs (SMul R (AlgQuotient (ModuleQuot.Con R r)))

instance [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M] : IsAddCommMagma (ModuleQuot R r) :=
  inferInstanceAs (IsAddCommMagma (AlgQuotient (ModuleQuot.Con R r)))

instance [MonoidOps R] [IsMonoid R] [Add M] [SMul R M] [IsMulAction R M] : IsMulAction R (ModuleQuot R r) :=
  inferInstanceAs (IsMulAction R (AlgQuotient (ModuleQuot.Con R r)))
instance [MonoidOps R] [IsMonoid R] [AddMonoidOps M] [IsAddMonoid M] [SMul R M] [IsDistribMulAction R M] : IsDistribMulAction R (ModuleQuot R r) :=
  inferInstanceAs (IsDistribMulAction R (AlgQuotient (ModuleQuot.Con R r)))
instance [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M] [SMul R M] [IsModule R M] : IsModule R (ModuleQuot R r) :=
  inferInstanceAs (IsModule R (AlgQuotient (ModuleQuot.Con R r)))

end

variable {r: M -> M -> Prop}

def mk (R: Type*) [AddMonoidOps M] [IsAddMonoid M] [SMul R M] (r: M -> M -> Prop) : M →ₗ[R] ModuleQuot R r :=
  LinearCon.mkQuot _

@[induction_eliminator]
def ind [AddMonoidOps M] [IsAddMonoid M] {motive: ModuleQuot R r -> Prop} (mk: ∀x, motive (mk R r x)) : ∀q, motive q := by
  intro q
  induction q using AlgQuotient.ind with
  | mk a =>
  apply mk

def mk_rel [AddMonoidOps M] [IsAddMonoid M] (w: r x y) : mk R r x = mk R r y := Quot.sound (LinearCon.Generator.of w)
def mk_surj [AddMonoidOps M] [IsAddMonoid M] : Function.Surjective (mk R r) := by
  intro a
  induction a with | mk a =>
  exists a

private def preLift [AddMonoidOps M] [IsAddMonoid M] [AddMonoidOps T] [IsAddMonoid T] [SMul R T] {r : M → M → Prop} {f : M →ₗ[R] T} (h : ∀ ⦃x y⦄, r x y → f x = f y) : ModuleQuot R r →ₗ[R] T where
  toFun := by
    refine  Quotient.lift f ?_
    intro a b g
    induction g with
    | of =>
      apply h
      assumption
    | refl => rfl
    | symm => symm; assumption
    | trans _ _ ih₀ ih₁ => rw [ih₀, ih₁]
    | smul =>
      rw [map_smul, map_smul]
      congr
    | add =>
      rw [map_add, map_add]
      congr
  map_add := by
    intro a b
    induction a; induction b
    apply map_add
  map_smul := by
    intro r a
    induction a
    apply map_smul

def lift
  [AddMonoidOps M] [IsAddMonoid M]
  [AddMonoidOps T] [IsAddMonoid T] [SMul R T]: {f: M →ₗ[R] T // ∀ ⦃x y⦄, r x y → f x = f y } ≃ (ModuleQuot R r →ₗ[R] T) where
  toFun f := preLift f.property
  invFun f := {
    val := f.comp (mk R r)
    property := by
      intro x y h
      show f (mk R r x) = f (mk R r y)
      congr 1; apply mk_rel
      assumption
  }
  leftInv _ := rfl
  rightInv f := by
    ext x; induction x
    rfl

@[simp]
def lift_mk_apply [AddMonoidOps M] [IsAddMonoid M] [AddMonoidOps T] [IsAddMonoid T] [SMul R T] (f : M →ₗ[R] T) {r : M → M → Prop} (w : ∀ ⦃x y⦄, r x y → f x = f y) (x) :
    lift ⟨f, w⟩ (mk R r x) = f x := rfl

def mkQuot_eq_mk [AddMonoidOps M] [IsAddMonoid M] : LinearCon.mkQuot (ModuleQuot.Con R r) = ModuleQuot.mk R r := rfl

attribute [irreducible] instAddMonoidOps instGroupOps instSMul mk lift

end ModuleQuot
