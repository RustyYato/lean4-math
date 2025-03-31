import Math.Algebra.Monoid.Con
import Math.Algebra.Group.Defs
import Math.Algebra.Monoid.Units.Defs

variable {C α: Type*} [RelLike C α] (c: C)

def resp_neg [AddGroupOps α] [IsAddGroup α] [IsAddCon C] (c: C) {a b: α} (h: c a b) : c (-a) (-b) := by
  let a' : AddUnits (IsCon.Quotient c) := {
    val := IsCon.mkQuot c a
    neg := IsCon.mkQuot c (-a)
    val_add_neg := by
      apply Quotient.sound
      rw [add_neg_cancel]
    neg_add_val := by
      apply Quotient.sound
      rw [neg_add_cancel]
  }
  let b' : AddUnits (IsCon.Quotient c) := {
    val := IsCon.mkQuot c b
    neg := IsCon.mkQuot c (-b)
    val_add_neg := by
      apply Quotient.sound
      rw [add_neg_cancel]
    neg_add_val := by
      apply Quotient.sound
      rw [neg_add_cancel]
  }
  have a'_eq_b' : a' = b' := by
    apply AddUnits.val_inj.mp
    apply Quotient.sound
    assumption
  apply Quotient.exact (s := IsCon.toSetoid c)
  show a'.neg = b'.neg
  rw [a'_eq_b']

def resp_zsmul [AddGroupOps α] [IsAddGroup α] [IsAddCon C] (c: C) (n: ℤ) {a b: α} (h: c a b) : c (n • a) (n • b) := by
  cases n
  rw [zsmul_ofNat, zsmul_ofNat]
  apply resp_nsmul
  assumption
  rw [zsmul_negSucc, zsmul_negSucc]
  apply resp_neg
  apply resp_nsmul
  assumption

def resp_sub [AddGroupOps α] [IsAddGroup α] [IsAddCon C] (c: C) {w x y z: α} (h: c w y) (g: c x z) : c (w - x) (y - z) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  apply resp_add
  assumption
  apply resp_neg
  assumption

def resp_inv [GroupOps α] [IsGroup α] [IsMulCon C] (c: C) {a b: α} (h: c a b) : c (a⁻¹) (b⁻¹) :=
  resp_neg (C := AddOfMul C) _ h

def resp_zpow [GroupOps α] [IsGroup α] [IsMulCon C] (c: C) (n: ℤ) {a b: α} (h: c a b) : c (a ^ n) (b ^ n) :=
  resp_zsmul (C := AddOfMul C) c n h

def resp_div [GroupOps α] [IsGroup α] [IsMulCon C] (c: C) {w x y z: α} (h: c w y) (g: c x z) : c (w / x) (y / z) :=
  resp_sub (C := AddOfMul C) c h g

instance [AddGroupOps α] [IsAddCon C] [IsAddGroup α] : Neg (IsCon.Quotient c) where
  neg := by
    apply Quotient.lift (fun a => IsCon.mkQuot c (-a))
    intro a b h
    apply Quotient.sound
    apply resp_neg
    assumption

instance [AddGroupOps α] [IsAddCon C] [IsAddGroup α] : SMul ℤ (IsCon.Quotient c) where
  smul n := by
    apply Quotient.lift (fun a => IsCon.mkQuot c (n • a))
    intro a b h
    apply Quotient.sound
    apply resp_zsmul
    assumption

instance [AddGroupOps α] [IsAddCon C] [IsAddGroup α] : Sub (IsCon.Quotient c) where
  sub := by
    apply Quotient.lift₂ (fun a b => IsCon.mkQuot c (a - b))
    intro a b c d h g
    apply Quotient.sound
    apply resp_sub
    assumption
    assumption

instance [GroupOps α] [IsMulCon C] [IsGroup α] : Inv (IsCon.Quotient c) where
  inv := by
    apply Quotient.lift (fun a => IsCon.mkQuot c (a⁻¹))
    intro a b h
    apply Quotient.sound
    apply resp_inv
    assumption

instance [GroupOps α] [IsMulCon C] [IsGroup α] : Pow (IsCon.Quotient c) ℤ where
  pow := flip <| by
    intro n
    apply Quotient.lift (fun a => IsCon.mkQuot c (a ^ n))
    intro a b h
    apply Quotient.sound
    apply resp_zpow
    assumption

instance [GroupOps α] [IsMulCon C] [IsGroup α] : Div (IsCon.Quotient c) where
  div := by
    apply Quotient.lift₂ (fun a b => IsCon.mkQuot c (a / b))
    intro a b c d h g
    apply Quotient.sound
    apply resp_div
    assumption
    assumption

instance [AddGroupOps α] [IsAddCon C] [IsAddGroup α] : IsAddGroup (IsCon.Quotient c) where
  sub_eq_add_neg a b := by
    induction a; induction b
    apply Quotient.sound
    rw [sub_eq_add_neg]
  neg_add_cancel a :=  by
    induction a
    apply Quotient.sound
    rw [neg_add_cancel]
  zsmul_ofNat n a := by
    induction a
    apply Quotient.sound
    rw [zsmul_ofNat]
  zsmul_negSucc n a := by
    induction a
    apply Quotient.sound
    rw [zsmul_negSucc]

instance [GroupOps α] [IsMulCon C] [IsGroup α] : IsGroup (IsCon.Quotient c) where
  div_eq_mul_inv := sub_eq_add_neg (α := (IsCon.Quotient (AddOfMul.mk c)))
  inv_mul_cancel := neg_add_cancel (α := (IsCon.Quotient (AddOfMul.mk c)))
  zpow_ofNat := zsmul_ofNat (α := (IsCon.Quotient (AddOfMul.mk c)))
  zpow_negSucc := zsmul_negSucc (α := (IsCon.Quotient (AddOfMul.mk c)))
