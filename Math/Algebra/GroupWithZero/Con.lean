import Math.Algebra.Monoid.Con
import Math.Algebra.GroupWithZero.Defs

variable {C α: Type*} [RelLike C α] (c: C)
   [GroupWithZeroOps α] [IsGroupWithZero α] [IsMulCon C]

def resp_inv? (c: C) {a b: α} (h: c a b) (ha: a ≠ 0) (hb: b ≠ 0) : c (a⁻¹?) (b⁻¹?) := by
  rw [←mul_one (a⁻¹?), ←mul_inv?_cancel b, ←mul_assoc]
  apply Relation.trans'
  apply resp_mul
  apply resp_mul
  rfl
  apply Relation.symm
  assumption
  rfl
  rw [inv?_mul_cancel, one_mul]

def resp_div? (c: C) {w x y z: α} (h: c w y) (g: c x z) (ha: x ≠ 0) (hb: z ≠ 0) : c (w /? x) (y /? z) := by
  rw [div?_eq_mul_inv?, div?_eq_mul_inv?]
  apply resp_mul
  assumption
  apply resp_inv?
  assumption

def resp_zpow? (c: C) (n: ℤ) {a b: α} (h: c a b) (ha: a ≠ 0 ∨ 0 ≤ n) (hb: b ≠ 0 ∨ 0 ≤ n) : c (a ^? n) (b ^? n) := by
  cases n
  rw [zpow?_ofNat, zpow?_ofNat]
  apply resp_npow
  assumption
  rw [zpow?_negSucc, zpow?_negSucc]
  apply resp_npow
  apply resp_inv?
  assumption
  apply hb.resolve_right
  omega
  apply ha.resolve_right
  omega

instance : CheckedInv? (IsCon.Quotient c) where
  checked_invert a := by
    refine Quotient.hrecOn a ?_ ?_
    intro a ha
    have : a ≠ 0 := by
      intro h; apply ha
      subst h; rfl
    exact IsCon.mkQuot c (a⁻¹?)
    intro a b h
    apply Function.hfunext
    rw [Quotient.sound h]
    intro ha hb eq
    simp
    apply Quotient.sound
    apply resp_inv?
    assumption

instance : CheckedDiv? (IsCon.Quotient c) where
  checked_div a b := by
    refine Quotient.liftOn a ?_ ?_
    intro a
    refine Quotient.hrecOn b ?_ ?_
    intro b hb
    have : b ≠ 0 := by
      intro h; apply hb
      subst h; rfl
    exact IsCon.mkQuot c (a /? b)
    intro b₀ b₁ h
    apply Function.hfunext
    rw [Quotient.sound h]
    intro h₀ h₁ g
    simp
    apply Quotient.sound
    apply resp_div?
    rfl; assumption
    intro a₀ a₁ h
    simp
    induction b with | mk b =>
    ext
    show IsCon.mkQuot c _ = IsCon.mkQuot c _
    apply Quotient.sound
    apply resp_div?
    assumption
    rfl

instance : CheckedIntPow? (IsCon.Quotient c) where
  checked_pow a n := by
    refine Quotient.hrecOn a ?_ ?_
    intro a ha
    have : a ≠ 0 ∨ 0 ≤ n := by
      rcases ha with ha | ha
      left; intro h; apply ha
      subst h; rfl
      right; assumption
    exact IsCon.mkQuot _ (a ^? n)
    intro a b h
    apply Function.hfunext
    rw [Quotient.sound h]
    intro ha hb g
    simp
    apply Quotient.sound
    apply resp_zpow?
    assumption

-- we can't prove that the quotient is non-trivial because this could have been the always
-- true relation. In which case, the quotient would be subsingleton
instance [IsNontrivial (IsCon.Quotient c)] : IsGroupWithZero (IsCon.Quotient c) where
  mul_inv?_cancel a _ := by
    induction a
    apply Quotient.sound
    rw [mul_inv?_cancel]
  div?_eq_mul_inv? a b _ := by
    induction a; induction b
    apply Quotient.sound
    rw [div?_eq_mul_inv?]
  zpow?_ofNat _ a := by
    induction a
    apply Quotient.sound
    rw [zpow?_ofNat]
  zpow?_negSucc _ a _ := by
    induction a
    apply Quotient.sound
    rw [zpow?_negSucc]
