import Math.Algebra.Group.Defs
import Math.Algebra.Monoid.Units.Defs

instance [MonoidOps α] [IsMonoid α] : Pow (Units α) ℤ where
  pow := flip zpowRec

instance [MonoidOps α] [IsMonoid α] : Div (Units α) where
  div := div'

instance [MonoidOps α] [IsMonoid α] : IsGroup (Units α) where
  mul_assoc := by
    intro a b c
    apply Units.val.inj
    apply mul_assoc
  one_mul := by
    intro a
    apply Units.val.inj
    apply one_mul
  mul_one := by
    intro a
    apply Units.val.inj
    apply mul_one
  div_eq_mul_inv _ _ := rfl
  zpow_ofNat _ _ := rfl
  zpow_negSucc _ _ := rfl
  inv_mul_cancel := by
    intro a
    apply Units.val.inj
    exact a.inv_mul_val
  npow_zero := by
    intro a
    apply Units.val.inj
    apply npow_zero
  npow_succ := by
    intro a n
    apply Units.val.inj
    apply npow_succ

instance [MonoidOps α] [AddGroupOps α] [IsMonoid α] [IsAddGroup α] [IsLeftDistrib α] [IsRightDistrib α] [IsMulZeroClass α] : Neg (Units α) where
  neg u := {
      val := -u.val
      inv := -u.inv
      val_mul_inv := by rw [mul_neg, neg_mul, neg_neg, u.val_mul_inv]
      inv_mul_val := by rw [mul_neg, neg_mul, neg_neg, u.inv_mul_val]
  }

instance [AddMonoidOps α] [IsAddMonoid α] : SMul ℤ (AddUnits α) where
  smul := zsmulRec

instance [AddMonoidOps α] [IsAddMonoid α] : Sub (AddUnits α) where
  sub := sub'

instance [AddMonoidOps α] [IsAddMonoid α] : IsAddGroup (AddUnits α) where
  add_assoc := by
    intro a b c
    apply AddUnits.val.inj
    apply add_assoc
  zero_add := by
    intro a
    apply AddUnits.val.inj
    apply zero_add
  add_zero := by
    intro a
    apply AddUnits.val.inj
    apply add_zero
  sub_eq_add_neg _ _ := rfl
  zsmul_ofNat _ _ := rfl
  zsmul_negSucc _ _ := rfl
  neg_add_cancel := by
    intro a
    apply AddUnits.val.inj
    exact a.neg_add_val
  zero_nsmul := by
    intro a
    apply AddUnits.val.inj
    apply zero_nsmul
  succ_nsmul := by
    intro a n
    apply AddUnits.val.inj
    apply succ_nsmul

instance [AddGroupOps α] [IsAddGroup α] [MonoidOps α] [IsMonoid α] : IsUnit (1: α) where
  eq_unit := ⟨1, rfl⟩

instance [AddGroupOps α] [IsAddGroup α] [MonoidOps α] [IsMonoid α] [IsLeftDistrib α] [IsRightDistrib α] [IsMulZeroClass α] (a: α) [IsUnit a] : IsUnit (-a: α) where
  eq_unit := by
    obtain ⟨a, rfl⟩ := IsUnit.eq_unit (x := a)
    exists -a

instance [AddGroupOps α] [IsAddGroup α] [MonoidOps α] [IsMonoid α] [IsLeftDistrib α] [IsRightDistrib α] [IsMulZeroClass α] (x: ℤ) [IsUnit x] (a: α) [IsUnit a] : IsUnit (x • a: α) := by
  rcases Int.ofIsUnit x with rfl | rfl
  rw [one_zsmul]; infer_instance
  rw [neg_one_zsmul]; infer_instance
