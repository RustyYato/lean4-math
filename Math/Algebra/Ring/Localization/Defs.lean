import Math.Algebra.Semiring.Localization.Defs
import Math.Algebra.Ring.Defs

namespace Localization

variable {R: Type*} [RingOps R] [IsRing R] [IsCommMagma R]
   (S: Submonoid R)

instance : Neg (Localization S) where
  neg := by
    refine Localization.lift S ?_ ?_
    · intro a b
      apply mk _ (-a) b
    · intro a₀ a₁ b₀ b₁ h
      rw [←neg_one_mul, ←neg_one_mul a₁,
        ←one_mul b₀, ←one_mul b₁]
      rw [←mk_mul, ←mk_mul, sound _ h]

def mk_neg (a b) : -mk S a b = mk S (-a) b := rfl

instance : Sub (Localization S) where
  sub := by
    refine Localization.lift₂ S ?_ ?_
    · intro a b c d
      apply mk
      exact d.val * a - b.val * c
      exact b * d
    · intro a₀ a₁ c₀ c₁ b₀ b₁ d₀ d₁ ab cd
      rw [sub_eq_add_neg, sub_eq_add_neg, ←mul_neg, ←mul_neg]
      rw [←mk_add, ←mk_add, ←mk_neg, ←mk_neg]
      rw [sound _ ab, sound _ cd]

instance : SMul ℤ (Localization S) where
  smul n := by
    refine Localization.lift S ?_ ?_
    intro a b
    exact mk S (n • a) b
    intro a c b d h
    cases n
    simp
    rw [zsmul_ofNat, zsmul_ofNat, ←mk_nsmul, ←mk_nsmul, sound _ h]
    simp
    rw [zsmul_negSucc, zsmul_negSucc, ←mk_neg, ←mk_neg,
      ←mk_nsmul, ←mk_nsmul, sound _ h]

instance : IntCast (Localization S) where
  intCast n := mk S n 1

def mk_sub (a b c d) : mk S a b - mk S c d = mk S (d.val * a - b.val * c) (b * d) := rfl

def mk_zsmul (n: ℤ) (a b) : n • mk S a b = mk S (n • a) b := rfl

def mk_intCast (n: ℤ) : n = mk S n 1 := rfl

instance : IsAddGroup (Localization S) where
  sub_eq_add_neg a b := by
    induction a with | mk a =>
    induction b with | mk b =>
    rw [mk_sub, sub_eq_add_neg, ←mul_neg]
    rfl
  neg_add_cancel a := by
    induction a with | mk a =>
    rw [mk_neg, mk_add, mul_neg, neg_add_cancel]
    apply zero_eq
  zsmul_ofNat n a := by
    induction a with | mk a =>
    rw [mk_zsmul, mk_nsmul, zsmul_ofNat]
  zsmul_negSucc n a := by
    induction a with | mk a =>
    rw [mk_zsmul, mk_nsmul, zsmul_negSucc]
    rfl

instance : IsAddGroupWithOne (Localization S) := {
  instIsAddMonoidWithOne S, instIsAddGroup S with
  intCast_ofNat n := by rw [mk_intCast, mk_natCast, intCast_ofNat]
  intCast_negSucc n := by rw [mk_intCast, mk_natCast, intCast_negSucc]; rfl
}

instance : IsRing (Localization S) := IsRing.inst

end Localization
