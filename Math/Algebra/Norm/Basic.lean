import Math.Algebra.Norm.Defs
import Math.Algebra.Field.Basic
import Math.Algebra.Field.Order.Basic

section

variable
  [Norm α β] [LE β] [LT β] [Min β] [Max β]
  [AddGroupOps α]
  [RingOps β] [IsRing β]
  [IsAddGroup α] [IsAddCommMagma α]
  [SMul β α] [IsModule β α]
  [IsOrderedSemiring β]
  [IsLinearLattice β] [IsLawfulNorm α]

def norm_ne_zero (a: α) : a ≠ 0 -> ‖a‖ ≠ 0 := by
  intro h g; apply h
  apply of_norm_eq_zero
  assumption

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply norm_ne_zero <;> invert_tactic)

end

section

variable
  [LE α] [LT α] [Min α] [Max α]
  [RingOps α] [IsRing α]
  [IsOrderedSemiring α]
  [IsLinearLattice α]

@[simp]
def abs_one : |(1: α)| = 1 := by
  apply flip le_antisymm
  apply le_max_left
  apply max_le
  rfl
  apply flip le_trans
  apply zero_le_one
  rw [neg_le_neg_iff, neg_neg, neg_zero]
  apply zero_le_one

def norm_eq_abs [Norm α α] [IsLawfulNorm α] (a: α) : ‖a‖ = |a| * ‖(1: α)‖ := by
  rw (occs := [1]) [←mul_one a]
  rw [←smul_eq_mul, norm_smul]

@[simp]
def abs_neg_one : |(-1: α)| = 1 := by
  apply flip le_antisymm
  rw (occs := [1]) [←neg_neg 1]
  apply le_max_right
  unfold abs
  rw [neg_neg]
  apply max_le
  refine neg_le_of_nonneg 1 ?_
  apply zero_le_one
  rfl

open Norm.ofAbs

def abs_mul (a b: α) : |a * b| = |a| * |b| := by
  apply norm_smul (α := α)

instance [IsCommMagma α] : IsAlgebraNorm α where
  norm_algebraMap _ := rfl
  norm_mul _ _ := by apply abs_mul

def abs_neg (a: α) : |-a| = |a| := by
  rw [←neg_one_mul, abs_mul]; simp

def abs_add_le_add_abs (a b: α): |a + b| ≤ |a| + |b| := norm_add_le_add_norm (α := α) _ _

def abs_zero_iff {a: α}: |a| = 0 ↔ a = 0 := norm_zero_iff (α := α)

def abs_zero : |(0: α)| = 0 := abs_zero_iff.mpr rfl
def of_abs_eq_zero {x: α} : |x| = 0 -> x = 0 := abs_zero_iff.mp

def abs_npow [IsNontrivial α] (a: α) (n: ℕ) : |a ^ n| = |a| ^ n := by
  induction n with
  | zero => rw [npow_zero, npow_zero, abs_one]
  | succ n ih => rw [npow_succ, abs_mul, ih, npow_succ]

def abs_npow_succ (a: α) (n: Nat) : |a ^ (n + 1)| = |a| ^ (n + 1) := by
  induction n with
  | zero => rw [npow_one, npow_one]
  | succ n ih => rw [npow_succ, npow_succ, abs_mul, ←npow_succ, ih, npow_succ, npow_succ, npow_succ]

def abs_unit [IsNontrivial α] (u: Units α) : Units α where
  val := |u.val|
  inv := |u.inv|
  val_mul_inv := by rw [←abs_mul, u.val_mul_inv, abs_one]
  inv_mul_val := by rw [←abs_mul, u.inv_mul_val, abs_one]

def abs_ne_zero (a: α) : a ≠ 0 -> |a| ≠ 0 := by
  intro h g; apply h
  apply of_abs_eq_zero
  assumption

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply abs_ne_zero <;> invert_tactic)

def abs_of_nonneg (a: α) : 0 ≤ a -> |a| = a := by
  intro h
  apply max_eq_left.mpr
  exact neg_le_of_nonneg a h

def abs_of_pos (a: α) : 0 < a -> |a| = a := by
  intro h
  apply abs_of_nonneg
  apply le_of_lt; assumption

def abs_sub_comm (a b: α) : |a - b| = |b - a| := by
  rw [←neg_sub, abs_neg]

def abs_add_le_abs_sub (a b: α) : 0 ≤ a -> b ≤ 0 -> |a + b| ≤ |a - b| := by
  intro h g
  apply max_le
  apply le_max_iff.mpr
  left; rw [sub_eq_add_neg]; apply add_le_add_left
  apply le_neg_of_nonpos; assumption
  rw [neg_add_rev]
  apply le_max_iff.mpr
  left
  rw [add_comm, sub_eq_add_neg]
  apply add_le_add_right
  apply neg_le_of_nonneg
  assumption

def abs_def [DecidableLE α] (a: α) : |a| = if 0 ≤ a then a else -a := by
  rw [abs]
  split; rw [max_eq_left.mpr];
  apply neg_le_of_nonneg; assumption
  rw [max_eq_right.mpr]
  apply le_neg_of_nonpos
  rw [not_le] at *
  apply le_of_lt
  assumption

def abs_nonneg (a: α) : 0 ≤ |a| := by
  apply le_max_iff.mpr
  rw (occs := [2]) [←neg_zero]; rw [neg_le_neg_iff]
  apply le_total

def abs_pos (a: α) : a ≠ 0 -> 0 < |a| := by
  intro h
  apply lt_of_le_of_ne
  apply abs_nonneg
  symm; invert_tactic

def le_abs_self (a: α) : a ≤ |a| := by
  apply le_max_left

def sub_abs_self_sub (a b: α) : a - |a - b| ≤ b := by
  rw [sub_le_iff_le_add, add_comm, le_add_iff_sub_le]
  apply le_abs_self

def abs_natCast (n: ℕ) : |(n: α)| = n := by
  rw [abs, max_eq_left]
  apply neg_le_of_nonneg
  exact natCast_nonneg n

@[norm_cast]
def abs_intCast (n: ℤ) : |(n: α)| = |n| := by
  cases n with
  | ofNat n =>
    rw [intCast_ofNat, abs_eq_natAbs, Int.natAbs_ofNat,
      abs_natCast, intCast_ofNat]
  | negSucc n =>
    rw [Int.negSucc_coe, ←intCast_neg, abs_neg,
      intCast_ofNat, abs_natCast, abs_neg,
      abs_eq_natAbs, intCast_ofNat, Int.natAbs_ofNat]

end

section

variable
  [LE α] [LT α] [Min α] [Max α]
  [FieldOps α] [IsNonCommField α]
  [IsOrderedSemiring α]
  [IsLinearLattice α]

def abs_inv? (a: α) (h: a ≠ 0) : |a⁻¹?| = |a|⁻¹? := by
  symm; apply inv?_eq_of_mul_left
  rw [←abs_mul, mul_inv?_cancel, abs_one]

def abs_div? (a b: α) (h: b ≠ 0) : |a /? b| = |a| /? |b| := by
  rw [div?_eq_mul_inv?, div?_eq_mul_inv?, abs_mul, abs_inv?]

def abs_div?_lt_one (a b: α) (h: b ≠ 0) : |a /? b| < 1 ↔ |a| < |b| := by
  rw [lt_iff_mul_lt_mul_of_pos_right _ _ |b|, one_mul, ←abs_mul, div?_eq_mul_inv?]
  rw [mul_assoc, inv?_mul_cancel, mul_one]
  exact abs_pos b h

end

section

variable
  [Norm α β] [LE β] [LT β] [Min β] [Max β]
  [AddGroupOps α]
  [RingOps β] [IsRing β]
  [IsAddGroup α] [IsAddCommMagma α]
  [SMul β α] [IsModule β α]
  [IsOrderedSemiring β]
  [IsLinearLattice β] [IsLawfulNorm α]

def norm_neg (a: α) : ‖-a‖ = ‖a‖ := by
  rw (occs := [1]) [←one_smul (R := β) a, ←neg_smul, norm_smul,
    abs_neg_one, one_mul]

def norm_sub_comm (a b: α) : ‖a - b‖ = ‖b - a‖ := by
  rw [←neg_sub, norm_neg]

def norm_nonneg (a: α) : 0 ≤ ‖a‖ := by
  have := norm_add_le_add_norm a (-a)
  rw [norm_neg, add_neg_cancel, norm_zero, le_add_iff_sub_le, zero_sub] at this
  rwa [neg_le_self] at this

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
  [Norm α β] [LE β] [LT β] [Min β] [Max β]
  [FieldOps β] [IsNonCommField β]
  [FieldOps α] [IsNonCommField α]
  [SMul β α] [AlgebraMap β α] [IsAlgebra β α]
  [IsOrderedSemiring β]
  [IsLinearLattice β] [h: IsAlgebraNorm α]

def norm_one : ‖(1: α)‖ = 1 := by
  rw [←map_one (algebraMap (R := β)), norm_algebraMap, abs_one]

def norm_div? (a b: α) (h: b ≠ 0) : ‖a /? b‖ = ‖a‖ /? ‖b‖ := by
  apply mul_right_cancel₀ (k := ‖b‖)
  invert_tactic
  rw [div?_mul_cancel, ←norm_mul, div?_mul_cancel]

def norm_inv? (a: α) (h: a ≠ 0) : ‖a⁻¹?‖ = ‖a‖⁻¹? := by
  apply inv?_eq_of_mul_right
  rw [←norm_mul, inv?_mul_cancel, norm_one]

end
