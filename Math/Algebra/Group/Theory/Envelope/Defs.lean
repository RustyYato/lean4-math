import Math.Data.Free.Group

inductive GroupEnvolope.Rel (α: Type*) [Mul α] : FreeGroup α -> FreeGroup α -> Prop where
| intro (a b: α) : Rel α (.of (a * b)) (.of a * .of b)

def GroupEnvolope (α: Type*) [Mul α] := GroupQuot (GroupEnvolope.Rel α)

namespace GroupEnvolope

instance instGroupOps [Mul α] : GroupOps (GroupEnvolope α) := inferInstanceAs (GroupOps (GroupQuot _))
instance [Mul α] : IsGroup (GroupEnvolope α) := inferInstanceAs (IsGroup (GroupQuot _))

structure ιType (α: Type*) where

def ι [Mul α] : MulHom α (GroupEnvolope α) where
  toFun := GroupQuot.mk _ ∘ FreeGroup.of
  map_mul {a b} := by
    simp; rw [←map_mul (GroupQuot.mk (Rel α)) (x := FreeGroup.of a) (y := FreeGroup.of b)]
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
   | of => apply ι
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
    simp [FreeGroup.lift_of, map_mul]
}

private def preLift_ι [Mul α] (f: MulHom α G) : preLift f (ι x) = f x := by
  show GroupEnvolope.preLift f (GroupQuot.mk _ (FreeGroup.of x)) = _
  erw [GroupQuot.lift_mk_apply, FreeGroup.lift_of]

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

def ι_one [Mul α] [One α] [IsMulOneClass α] : ι (1: α) = 1 := by
  rw [←inv_mul_cancel (ι 1)]
  apply mul_left_cancel (k := ι 1)
  rw [←map_mul, ←mul_assoc, mul_inv_cancel, one_mul, one_mul]

def ιHom [Mul α] [One α] [IsMulOneClass α] : α →* GroupEnvolope α := {
  ι with
  map_one := ι_one
}

def ι_eq_ιHom [Mul α] [One α] [IsMulOneClass α]: (ι: α -> _) = (ιHom: α -> _) := rfl

def liftHom [Mul α] [One α] [IsMulOneClass α] : (α →* G) ≃ (GroupEnvolope α →* G) where
  toFun f := lift f
  invFun f := {
    lift.symm f with
    map_one := by
      simp
      rw [lift]
      simp
      show f (ι 1) = _
      rw [ι_eq_ιHom, map_one, map_one]
  }
  leftInv x := by
    simp
    rfl
  rightInv x := by
    simp
    show lift (lift.symm x) = x
    simp

end GroupEnvolope

-- every homomorphism to a group that preserves products also preserves the unit
instance [Mul α] [One α] [IsMulOneClass α] [GroupOps β] [IsGroup β] [FunLike F α β] [IsMulHom F α β] : IsOneHom F α β where
  map_one f := by
    let h : MulHom α β ≃ (α →* β) := GroupEnvolope.lift.trans GroupEnvolope.liftHom.symm
    have : (f: α -> β) = h (toMulHom f) := by
      show (f: α -> β) = GroupEnvolope.lift.symm (GroupEnvolope.lift (toMulHom f))
      simp
      rfl
    rw [this, map_one]
