import Math.Algebra.Abs.Defs

def MaxBool := Bool

instance : SemiringOps MaxBool where
  add := or
  mul := and
  zero := false
  one := true
  natCast n := n != 0
  ofNat _ := ⟨true⟩
  nsmul n x := and (n != 0) x
  npow
  | _, 0 => true
  | x, _ => x

instance : DecidableEq MaxBool := inferInstanceAs (DecidableEq Bool)
instance {P: MaxBool -> Prop} [DecidablePred P] : Decidable (∃x, P x) := inferInstanceAs (Decidable (∃x: Bool, P x))
instance {P: MaxBool -> Prop} [DecidablePred P] : Decidable (∀x, P x) := inferInstanceAs (Decidable (∀x: Bool, P x))

instance : IsSemiring MaxBool where
  add_comm := by trivial
  add_assoc := by trivial
  add_zero := by trivial
  zero_add := by trivial
  natCast_zero := rfl
  natCast_succ := by
    intro n
    show true = or _ true
    simp
  mul_assoc := by trivial
  ofNat_eq_natCast _ := by trivial
  zero_mul := by trivial
  mul_zero := by trivial
  one_mul := by trivial
  mul_one := by trivial
  left_distrib := by trivial
  right_distrib := by trivial
  zero_nsmul := by trivial
  succ_nsmul n a := by
    show and _ _ = or (and _ _) _
    simp
  npow_zero := by trivial
  npow_succ n a := by
    show a = and _ _
    cases n
    rfl
    show _ = and a a
    decide +revert

instance : IsCommMagma MaxBool where
  mul_comm := by decide

instance : LE MaxBool := inferInstanceAs (LE Bool)
instance : LT MaxBool := inferInstanceAs (LT Bool)
instance : IsLinearOrder MaxBool := inferInstanceAs (IsLinearOrder Bool)

instance : DecidableLE MaxBool := inferInstanceAs (DecidableLE Bool)

instance : IsOrderedSemiring MaxBool where
  add_le_add_left := by decide
  mul_nonneg := by decide
  mul_le_mul_of_nonneg_left := by decide
  mul_le_mul_of_nonneg_right := by decide
  zero_le_one := by decide

instance : Bot MaxBool := ⟨0⟩
instance : IsLawfulBot MaxBool := ⟨by decide⟩

namespace AbsoluteValue.Trivial

variable [DecidableEq α] [AddMonoidOps α] [Mul α]
  [IsNonUnitalNonAssocSemiring α] [NoZeroDivisors α]

scoped instance : AbsoluteValue α MaxBool where
  abs a := if a = 0 then 0 else 1

scoped instance : IsLawfulAbs α where
  abs_nonneg := by
    intro
    apply bot_le
  abs_zero_iff := by
    intro a
    simp [AbsoluteValue.abs]
  abs_mul := by
    intro a b
    simp [AbsoluteValue.abs]
    split <;> rename_i h
    rcases of_mul_eq_zero h with h | h <;> rw [if_pos h]
    rw [zero_mul]
    rw [mul_zero]
    split <;> rename_i ha
    rw [ha, zero_mul] at h; contradiction
    split <;> rename_i hb
    rw [hb, mul_zero] at h; contradiction
    rfl
  abs_add_le_add_abs := by
    intro a b
    by_cases ha:a = 0
    simp [AbsoluteValue.abs, ha]
    simp [AbsoluteValue.abs]
    split
    apply bot_le
    apply le_refl

end AbsoluteValue.Trivial
