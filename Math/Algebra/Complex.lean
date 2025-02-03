import Math.Data.Complex.Defs

namespace Complex

attribute [local simp] add_zero zero_add mul_zero zero_mul one_mul mul_one sub_zero neg_add_rev mul_add add_mul

instance : IsField ℂ where
  zero_ne_one := by
    intro h
    obtain ⟨h, _⟩ := Complex.mk.inj h
    exact zero_ne_one h
  add_comm _ _ := by ext <;> apply add_comm
  add_assoc _ _ _ := by ext <;> apply add_assoc
  mul_comm := by
    intro a b
    ext
    show _ - _ = _ - _
    rw [mul_comm, mul_comm a.img]
    show _ + _ = _ + _
    rw [mul_comm, mul_comm a.img, add_comm]
  mul_assoc a b c := by
    ext
    simp [sub_eq_add_neg, ←neg_mul_left, ←neg_mul_right]
    ac_rfl
    simp [sub_eq_add_neg, ←neg_mul_left, ←neg_mul_right]
    ac_rfl
  zero_add := by intro a; ext <;> simp
  add_zero := by intro a; ext <;> simp
  mul_one := by intro a; ext <;> simp
  one_mul := by intro a; ext <;> simp
  mul_zero := by intro a; ext <;> simp
  zero_mul := by intro a; ext <;> simp
  left_distrib := by
    intro k a b
    ext <;> simp [sub_eq_add_neg]
    ac_rfl
    ac_rfl
  right_distrib := by
    intro k a b
    ext <;> simp [sub_eq_add_neg]
    ac_rfl
    ac_rfl
  sub_eq_add_neg a b := by
    ext <;> simp [sub_eq_add_neg]
  neg_add_cancel a := by
    ext <;> simp [neg_add_cancel]
  mul_inv?_cancel a h := by
    ext <;> simp [mul_inv?_cancel]
    rw [div?_eq_mul_inv?, div?_eq_mul_inv?,
      ←mul_assoc, ←mul_assoc, ←sub_mul, ←neg_mul_right, sub_eq_add_neg,
      neg_neg, ←mag_sq, mul_inv?_cancel]
    rw [div?_eq_mul_inv?, div?_eq_mul_inv?,
      ←mul_assoc, ←mul_assoc, ←add_mul, ←neg_mul_right, mul_comm a.img,
      neg_add_cancel, zero_mul]
  zero_nsmul a := by
    show 0 * a = 0
    ext <;> simp
  succ_nsmul n a := by
    show (n + 1: ℕ) * a = n * a + a
    ext
    simp; rw [natCast_mul_eq_nsmul, succ_nsmul]; rfl
    simp; rw [natCast_mul_eq_nsmul, succ_nsmul]; rfl
  zsmul_ofNat _ _ := rfl
  zsmul_negSucc n a := by
    ext <;> simp [zsmul_def]
    rw [intCast_mul_eq_zsmul, zsmul_negSucc]
    simp [nsmul_def]; rfl
    rw [intCast_mul_eq_zsmul, zsmul_negSucc]
    simp [nsmul_def]; rfl
  zpow?_ofNat _ _ := rfl
  zpow?_negSucc _ _ _ := rfl
  natCast_zero := rfl
  natCast_succ n := by
    ext <;> simp
    rw [natCast_succ]
  intCast_ofNat n := rfl
  intCast_negSucc _ := rfl
  div?_eq_mul_inv? _ _ _ := rfl
  ofNat_eq_natCast _ := rfl

end Complex
