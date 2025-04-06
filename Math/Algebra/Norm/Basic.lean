import Math.Algebra.Norm.Defs
import Math.Algebra.Field.Basic
import Math.Algebra.Field.Order.Basic

section

variable {α γ: Type*}
  [Norm α γ] [LatticeOps γ] [SemiringOps γ] [IsSemiring γ]
  [AddGroupOps α] [IsAddGroup α] [IsAddCommMagma α]
  [IsOrderedSemiring γ] [IsLinearLattice γ] [IsLawfulNorm α]

def norm_ne_zero (a: α) : a ≠ 0 -> ‖a‖ ≠ 0 := by
  intro h g; apply h
  apply of_norm_eq_zero
  assumption

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply norm_ne_zero <;> invert_tactic)

def norm_sub_comm (a b: α) : ‖a - b‖ = ‖b - a‖ := by
  rw [←neg_sub, norm_neg]

def norm_nonneg (a: α) : 0 ≤ ‖a‖ := by
  have := norm_add_le_add_norm a (-a)
  rw [norm_neg, add_neg_cancel, norm_zero] at this
  rw [←not_lt]
  intro h
  have : ‖a‖ + ‖a‖ ≤ ‖a‖ + 0 := by
    apply add_le_add_left
    apply le_of_lt; assumption
  rw [add_zero] at this
  have := not_le_of_lt (lt_of_le_of_lt this h)
  contradiction

end

section

variable {α γ: Type*}
  [Norm α γ] [LatticeOps γ] [RingOps γ] [IsRing γ]
  [AddGroupOps α] [IsAddGroup α] [IsAddCommMagma α]
  [IsOrderedSemiring γ] [IsLinearLattice γ] [IsLawfulNorm α]

def abs_norm_sub_norm_le_norm_sub (a b: α) : |‖a‖ - ‖b‖| ≤ ‖a - b‖ := by
  have v₀ := norm_add_le_add_norm (a - b) b
  rw [sub_add_cancel, le_add_iff_sub_le] at v₀
  have v₁ := norm_add_le_add_norm (b - a) a
  rw [sub_add_cancel, le_add_iff_sub_le, norm_sub_comm] at v₁
  classical
  rw [abs_def]
  split
  assumption
  rw [neg_sub]
  assumption

end

section

variable
  [Norm α γ] [LatticeOps γ] [SemifieldOps γ] [IsSemifield γ]
  [FieldOps α] [IsField α]
  [IsOrderedSemiring γ] [IsLinearLattice γ] [h: IsAlgebraNorm α]

def norm_div? (a b: α) (h: b ≠ 0) : ‖a /? b‖ = ‖a‖ /? ‖b‖ := by
  apply mul_right_cancel₀ (k := ‖b‖)
  invert_tactic
  rw [div?_mul_cancel, ←norm_mul, div?_mul_cancel]

def norm_inv? (a: α) (h: a ≠ 0) : ‖a⁻¹?‖ = ‖a‖⁻¹? := by
  apply inv?_eq_of_mul_right
  rw [←norm_mul, inv?_mul_cancel, norm_one]

end
