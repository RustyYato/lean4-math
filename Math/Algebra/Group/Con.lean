import Math.Algebra.Monoid.Con
import Math.Algebra.Group.Defs
import Math.Algebra.Monoid.Units.Defs

variable {C α: Type*} [RelLike C α] (c: C)

def resp_neg [AddGroupOps α] [IsAddGroup α] [IsAddCon C] (c: C) {a b: α} (h: c a b) : c (-a) (-b) := by
  rw [←add_zero (-a), ←add_neg_cancel b, ←add_assoc]
  apply Relation.trans'
  apply resp_add
  apply resp_add
  rfl
  apply Relation.symm
  assumption
  rfl
  rw [neg_add_cancel, zero_add]

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

instance [AddGroupOps α] [IsAddGroup α] [IsAddCon C] : IsSMulCon C ℤ where
  resp_smul := resp_zsmul

instance [AddGroupOps α] [IsAddCon C] [IsAddGroup α] : Neg (AlgQuotient c) where
  neg := by
    apply Quotient.lift (fun a => IsCon.mkQuot c (-a))
    intro a b h
    apply Quotient.sound
    apply resp_neg
    assumption

instance [AddGroupOps α] [IsAddGroup α] [IsAddCon C] : SMul ℤ (AlgQuotient c) := inferInstance

instance [AddGroupOps α] [IsAddCon C] [IsAddGroup α] : Sub (AlgQuotient c) where
  sub := by
    apply Quotient.lift₂ (fun a b => IsCon.mkQuot c (a - b))
    intro a b c d h g
    apply Quotient.sound
    apply resp_sub
    assumption
    assumption

instance [GroupOps α] [IsMulCon C] [IsGroup α] : Inv (AlgQuotient c) where
  inv := by
    apply Quotient.lift (fun a => IsCon.mkQuot c (a⁻¹))
    intro a b h
    apply Quotient.sound
    apply resp_inv
    assumption

instance [GroupOps α] [IsMulCon C] [IsGroup α] : Pow (AlgQuotient c) ℤ where
  pow := flip <| by
    intro n
    apply Quotient.lift (fun a => IsCon.mkQuot c (a ^ n))
    intro a b h
    apply Quotient.sound
    apply resp_zpow
    assumption

instance [GroupOps α] [IsMulCon C] [IsGroup α] : Div (AlgQuotient c) where
  div := by
    apply Quotient.lift₂ (fun a b => IsCon.mkQuot c (a / b))
    intro a b c d h g
    apply Quotient.sound
    apply resp_div
    assumption
    assumption

instance AlgQuotient.instAddGroupOps [AddGroupOps α] [IsAddGroup α] [IsAddCon C]: AddGroupOps (AlgQuotient c) := inferInstance

instance AlgQuotient.instIsAddGroup [AddGroupOps α] [IsAddCon C] [IsAddGroup α] : IsAddGroup (AlgQuotient c) where
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

instance AlgQuotient.instGroupOps [GroupOps α] [IsGroup α] [IsMulCon C]: GroupOps (AlgQuotient c) := inferInstance

instance AlgQuotient.instIsGroup [GroupOps α] [IsMulCon C] [IsGroup α] : IsGroup (AlgQuotient c) where
  div_eq_mul_inv := sub_eq_add_neg (α := (AlgQuotient (AddOfMul.mk c)))
  inv_mul_cancel := neg_add_cancel (α := (AlgQuotient (AddOfMul.mk c)))
  zpow_ofNat := zsmul_ofNat (α := (AlgQuotient (AddOfMul.mk c)))
  zpow_negSucc := zsmul_negSucc (α := (AlgQuotient (AddOfMul.mk c)))
