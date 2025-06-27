import Math.Data.Free.Group

inductive GroupEnvolope.Rel (α: Type*) [Mul α] : FreeGroup α -> FreeGroup α -> Prop where
| intro (a b: α) : Rel α (.ι (a * b)) (.ι a * .ι b)

def GroupEnvolope (α: Type*) [Mul α] := GroupQuot (GroupEnvolope.Rel α)

namespace GroupEnvolope

instance instGroupOps [Mul α] : GroupOps (GroupEnvolope α) := inferInstanceAs (GroupOps (GroupQuot _))
instance [Mul α] : IsGroup (GroupEnvolope α) := inferInstanceAs (IsGroup (GroupQuot _))

structure ιType (α: Type*) where

def ι [Mul α] : MulHom α (GroupEnvolope α) where
  toFun := GroupQuot.mk _ ∘ FreeGroup.ι
  map_mul {a b} := by
    simp; rw [←map_mul (GroupQuot.mk (Rel α)) (x := FreeGroup.ι a) (y := FreeGroup.ι b)]
    apply GroupQuot.mk_rel
    apply Rel.intro

@[induction_eliminator]
def induction [Mul α] {motive: GroupEnvolope α -> Prop}
   (one: motive 1)
   (ι: ∀a: α, motive (ι a))
   (inv: ∀a: α, motive (.ι a) -> motive ((.ι a)⁻¹))
   (mul: ∀a b: GroupEnvolope α, motive a -> motive b -> motive (a * b)) :
   ∀g, motive g := by
   intro g
   induction g using GroupQuot.ind with | mk g =>
   induction g with
   | one => rw [map_one]; apply one
   | ι => apply ι
   | inv =>
      rw [map_inv]
      apply inv
      assumption
   | mul =>
    rw [map_mul]
    apply mul
    assumption
    assumption

instance [Mul α] [IsCommMagma α] : IsCommMagma (GroupEnvolope α) where
  mul_comm a b := by
    induction a with
    | one => simp
    | mul a₀ a₁ ih₀ ih₁ => rw [mul_assoc, ih₁, ←mul_assoc, ih₀, mul_assoc]
    | ι a =>
      induction b with
      | one => simp
      | ι b => rw [←map_mul, ←map_mul, mul_comm]
      | inv b ih =>
        apply mul_right_cancel (k := ι b)
        rw [mul_assoc, mul_assoc, ih, ←mul_assoc _ (ι b)]
        simp
      | mul b₀ b₁ ih₀ ih₁ => rw [mul_assoc, ←ih₁, ←mul_assoc b₀, ←ih₀, mul_assoc]
    | inv a ih =>
      apply mul_left_cancel (k := ι a)
      rw [←mul_assoc, ←mul_assoc, ih, mul_assoc b]
      simp

variable [GroupOps G] [IsGroup G]

private def preLift [Mul α] (f: MulHom α G) : GroupEnvolope α →* G := GroupQuot.lift {
  val := FreeGroup.lift f
  property {a b} h := by
    cases h
    simp [FreeGroup.apply_lift_ι, map_mul]
}

private def preLift_ι [Mul α] (f: MulHom α G) : preLift f (ι x) = f x := by
  show GroupEnvolope.preLift f (GroupQuot.mk _ (.ι x)) = _
  erw [GroupQuot.lift_mk_apply, FreeGroup.apply_lift_ι]

def lift [Mul α] : MulHom α G ≃ (GroupEnvolope α →* G) where
  toFun := preLift
  invFun f := f.toMulHom.comp ι
  leftInv f := by
    simp; apply DFunLike.ext
    intro x; apply preLift_ι
  rightInv f := by
    simp
    ext x
    induction x with
    | one => rw [map_one, map_one]
    | inv a ih => rw [map_inv, map_inv, ih]
    | mul a b iha ihb => rw [map_mul, map_mul, iha, ihb]
    | ι a =>
      rw [preLift_ι]
      rfl

def apply_lift_ι [Mul α] (f: MulHom α G) : lift f (ι x) = f x := by apply preLift_ι

attribute [irreducible] GroupEnvolope lift instGroupOps ι

def liftHom [Mul α] [One α] [IsMulOneClass α] : (α →* G) ≃ (GroupEnvolope α →* G) where
  toFun f := lift f.toMulHom
  invFun f := {
    lift.symm f with
    map_one := by
      simp
      rw [lift]
      simp
      show f (ι 1) = _
      rw [map_one, map_one]
  }
  leftInv x := by
    simp
    rfl
  rightInv x := by
    simp
    show lift (lift.symm x) = x
    simp

def apply_liftHom_ι [Mul α] [One α] [IsMulOneClass α] (f: α →*  G) : liftHom f (ι x) = f x := by apply apply_lift_ι

def equivGroup : GroupEnvolope G ≃* G := {
  liftHom (GroupHom.id _) with
  invFun := ι
  leftInv x := by
    simp
    induction x with
    | one => rw [map_one, map_one]
    | ι a =>
      rw [apply_liftHom_ι]
      rfl
    | inv a ih => rw [map_inv, map_inv, ih]
    | mul a b iha ihb => rw [map_mul, map_mul, iha, ihb]
  rightInv x := by
    simp
    rw [apply_liftHom_ι]
    rfl
}

end GroupEnvolope
