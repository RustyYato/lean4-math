import Math.Algebra.Monoid.Localization.Defs
import Math.Algebra.Semiring.Defs

namespace Localization

variable {R: Type*} [SemiringOps R] [IsSemiring R] [IsCommMagma R]
   (S: Submonoid R)

instance : Add (Localization S) where
  add := by
    refine Localization.lift₂ S ?_ ?_
    · intro a b c d
      apply mk
      exact d.val * a + b.val * c
      exact b * d
    · intro a₀ a₁ c₀ c₁ b₀ b₁ d₀ d₁
      repeat rw [Localization.con_iff_exists]
      intro ⟨x, ab⟩ ⟨y, cd⟩
      simp at ab cd
      apply sound; rw [Localization.con_iff_exists]
      simp
      exists x * y
      show (x.val * y.val) * ((b₁.val * _) * _) = (x.val * y.val) * ((b₀.val * _) * _)
      repeat rw [mul_add]
      congr 1
      rw [show x.val * y.val * (b₁.val * d₁.val * (d₀.val * a₀)) =
        (x.val * (b₁.val * a₀)) * (y.val * (d₁.val * d₀.val)) by ac_rfl]
      rw [ab]; ac_rfl

      rw [show x.val * y.val * (b₁.val * d₁.val * (b₀.val * c₀)) =
        (y.val * (d₁.val * c₀)) * (x.val * (b₁.val * b₀.val)) by ac_rfl]
      rw [cd]; ac_rfl

instance : SMul ℕ (Localization S) where
  smul n := by
    refine Localization.lift S ?_ ?_
    intro a b
    exact mk S (n • a) b
    intro a c b d h
    apply sound
    rw [Localization.con_iff_exists] at *
    obtain ⟨x, h⟩ := h
    simp at h
    exists x
    simp
    rw [nsmul_eq_natCast_mul, nsmul_eq_natCast_mul]
    repeat rw [←mul_left_comm (n: R)]
    rw [h]

instance : Zero (Localization S) where
  zero := mk S 0 1

instance : NatCast (Localization S) where
  natCast n := mk S n 1

def mk_add (a b c d) : mk S a b + mk S c d = mk S (d.val * a + b.val * c) (b * d) := rfl

def mk_nsmul (n: ℕ) (a b) : n • mk S a b = mk S (n • a) b := rfl

def mk_zero : 0 = mk S 0 1 := rfl

def mk_natCast (n: ℕ) : n = mk S n 1 := rfl

def zero_eq (b₀ b₁: S) : mk S 0 b₀ = mk S 0 b₁ := by
  revert b₀ b₁
  suffices ∀b, mk S 0 1 = mk S 0 b by
    intro a b; rw [←this a, ←this b]
  intro b
  rw (occs := [2]) [←zero_mul b.val]
  rw (occs := [2]) [←one_mul b]
  rw [mk_mul_cancel_right]

instance : IsAddMonoid (Localization S) where
  add_assoc a b c := by
    induction a with | mk a =>
    induction b with | mk b =>
    induction c with | mk c =>
    simp [mk_add, mul_add]
    ac_rfl
  zero_add a := by
    induction a with | mk a =>
    simp [mk_zero, mk_add]
  add_zero a := by
    induction a with | mk a =>
    simp [mk_zero, mk_add]
  zero_nsmul a := by
    induction a with | mk a b =>
    simp [mk_zero, mk_nsmul]
    apply zero_eq
  succ_nsmul n a := by
    induction a with | mk a b =>
    simp [mk_nsmul, succ_nsmul, mk_add]
    rw [←mul_add, mk_mul_cancel_left]

instance : IsAddMonoidWithOne (Localization S) where
  natCast_zero := by rw [mk_zero, mk_natCast, natCast_zero]
  natCast_succ n := by simp [mk_natCast, mk_one, mk_add, natCast_succ]

instance : IsAddCommMagma (Localization S) where
  add_comm a b := by
    induction a with | mk a =>
    induction b with | mk b =>
    simp [mk_add, add_comm, mul_comm]

instance : IsMulZeroClass (Localization S) where
  mul_zero a := by
    induction a with | mk a =>
    simp [mk_zero, mk_mul]
    apply zero_eq
  zero_mul a := by
    induction a with | mk a =>
    simp [mk_zero, mk_mul]
    apply zero_eq

instance : IsLeftDistrib (Localization S) where
  mul_add k a b := by
    induction k with | mk k₀ k₁ =>
    induction a with | mk a₀ a₁ =>
    induction b with | mk b₀ b₁ =>
    simp [mk_mul, mk_add]
    rw [mul_add, mul_assoc k₁.val, mul_assoc k₁.val,
      mul_assoc k₁, ←mul_add k₁.val, mk_mul_cancel_left]
    ac_rfl

instance : IsSemiring (Localization S) := IsSemiring.inst

end Localization
