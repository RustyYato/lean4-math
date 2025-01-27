import Math.Algebra.Ring
import Math.Order.Linear
import Math.Ops.Abs
import Math.Data.StdInt.AbsoluteValue

variable (α: Type*) [LT α] [LE α] [Add α] [Zero α] [SMul ℕ α] [Mul α] [One α] [Pow α ℕ]
variable {α₀: Type*} [LT α₀] [LE α₀] [Add α₀] [Zero α₀] [SMul ℕ α₀] [Mul α₀] [One α₀] [Pow α₀ ℕ]

class IsOrderedAddCommMonoid extends IsAddCommMagma α, IsAddMonoid α, IsPartialOrder α : Prop where
  add_le_add_left : ∀ a b : α, a ≤ b → ∀ c, c + a ≤ c + b
  le_iff_nsmul_le: ∀a b: α, ∀n > 0, a ≤ b ↔ n • a ≤ n • b

class IsOrderedCommMonoid extends IsCommMagma α, IsMonoid α, IsPartialOrder α : Prop where
  mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c, c * a ≤ c * b

export IsOrderedAddCommMonoid (
  le_iff_nsmul_le
)

def add_le_add_left [IsOrderedAddCommMonoid α₀] : ∀ a b : α₀, a ≤ b → ∀ c, c + a ≤ c + b := IsOrderedAddCommMonoid.add_le_add_left
def add_le_add_right [IsOrderedAddCommMonoid α₀] : ∀ a b : α₀, a ≤ b → ∀ c, a + c ≤ b + c := by
  intro a b a_le_b c
  rw [add_comm _ c, add_comm _ c]
  apply add_le_add_left
  assumption

def add_le_add [IsOrderedAddCommMonoid α₀] : ∀a b c d: α₀, a ≤ c -> b ≤ d -> a + b ≤ c + d := by
  intro a b c d ac bd
  apply le_trans
  apply add_le_add_left
  assumption
  apply add_le_add_right
  assumption

def mul_le_mul_left  [IsOrderedCommMonoid α₀] : ∀ a b : α₀, a ≤ b → ∀ c, c * a ≤ c * b := IsOrderedCommMonoid.mul_le_mul_left
def mul_le_mul_right [IsOrderedCommMonoid α₀] : ∀ a b : α₀, a ≤ b → ∀ c, a * c ≤ b * c := by
  intro a b a_le_b c
  rw [mul_comm _ c, mul_comm _ c]
  apply mul_le_mul_left
  assumption

def mul_le_mul [IsOrderedCommMonoid α₀] : ∀a b c d: α₀, a ≤ c -> b ≤ d -> a * b ≤ c * d := by
  intro a b c d ac bd
  apply le_trans
  apply mul_le_mul_left
  assumption
  apply mul_le_mul_right
  assumption

variable [NatCast α] [∀n, OfNat α (n + 2)]
variable [NatCast α₀] [∀n, OfNat α₀ (n + 2)]

class IsOrderedSemiring extends IsSemiring α, IsOrderedAddCommMonoid α where
  zero_le_one: 0 ≤ (1: α)
  mul_le_mul_of_nonneg_left: ∀a b: α, a ≤ b -> ∀c, 0 ≤ c -> c * a ≤ c * b
  mul_le_mul_of_nonneg_right: ∀a b: α, a ≤ b -> ∀c, 0 ≤ c -> a * c ≤ b * c

export IsOrderedSemiring (zero_le_one mul_le_mul_of_nonneg_left mul_le_mul_of_nonneg_right)

def zero_lt_one [IsOrderedSemiring α₀] [IsNontrivial α₀] : (0: α₀) < 1 := lt_of_le_of_ne zero_le_one zero_ne_one

variable [Sub α] [SMul ℤ α] [Neg α] [IntCast α]
variable [Sub α₀] [SMul ℤ α₀] [Neg α₀] [IntCast α₀]

class IsOrderedRing extends IsRing α, IsOrderedSemiring α where
  mul_nonneg: ∀a b: α, 0 ≤ a -> 0 ≤ b -> 0 ≤ a * b

class IsStrictOrderedRing extends IsRing α, IsOrderedRing α, IsNontrivial α where
  mul_pos: ∀a b: α, 0 < a -> 0 < b -> 0 < a * b

class IsLawfulAbs [AbsoluteValue α β] [LT β] [LE β] [Zero β] extends IsLinearOrder β where
  abs_nonneg: ∀a: α, 0 ≤ ‖a‖

variable [LT β] [LE β] [Zero β] [Add β] [SMul ℕ β] [One β] [Mul β] [Pow β ℕ]

class IsOrderedAbsAddMonoid [IsAddMonoid α] [IsOrderedAddCommMonoid β] [AbsoluteValue α β] extends IsLawfulAbs α where
  abs_zero: ∀{x: α}, ‖x‖ = 0 ↔ x = 0
  abs_add_le_add_abs: ∀a b: α, ‖a + b‖ ≤ ‖a‖ + ‖b‖
  nsmul_abs: ∀a: α, ∀n: Nat, ‖n • a‖ = n • ‖a‖

class IsOrderedAbsMonoid [IsMonoid α] [IsMonoid β] [AbsoluteValue α β] extends IsLawfulAbs α where
  abs_one: ‖(1: α)‖ = 1
  mul_abs: ∀a b: α, ‖a * b‖ = ‖a‖ * ‖b‖

export IsOrderedAbsAddMonoid (abs_zero abs_add_le_add_abs nsmul_abs)

export IsOrderedAbsMonoid (abs_one mul_abs)

class IsOrderedAbsAddGroup [IsAddGroup α] [IsOrderedAddCommMonoid β] [AbsoluteValue α β] extends IsOrderedAbsAddMonoid α where
  neg_abs: ∀a: α, ‖-a‖ = ‖a‖

export IsOrderedAbsAddGroup (neg_abs)

variable [Mul β] [One β] [Pow β ℕ] [NatCast β] [∀n, OfNat β (n + 2)]

class IsOrderedAbsSemiring [IsSemiring α] [IsOrderedSemiring β] [AbsoluteValue α β] extends IsOrderedAbsAddMonoid α, IsOrderedAbsMonoid α where
  natcast_abs: ∀n: Nat, ‖(n: α)‖ = n

export IsOrderedAbsSemiring (natcast_abs)

class IsOrderedAbsRing [IsRing α] [IsOrderedSemiring β] [AbsoluteValue α β] extends IsOrderedAbsSemiring α, IsOrderedAbsAddGroup α where
  intcast_abs: ∀n: Int, ‖(n: α)‖ = ‖n‖

export IsOrderedAbsRing (intcast_abs)

section

variable [IsAddMonoid α] [IsOrderedAddCommMonoid β] [AbsoluteValue α β] [IsOrderedAbsAddMonoid α]

def add_lt_add_left [IsAddLeftCancel β] (a b k: β) : a < b -> k + a < k + b := by
  intro h
  apply lt_of_le_of_ne
  apply add_le_add_left
  apply le_of_lt; assumption
  intro g
  rw [add_left_cancel g] at h
  exact lt_irrefl h

def add_lt_add_right [IsAddRightCancel β] (a b k: β) : a < b -> a + k < b + k := by
  intro h
  apply lt_of_le_of_ne
  apply add_le_add_right
  apply le_of_lt; assumption
  intro g
  rw [add_right_cancel g] at h
  exact lt_irrefl h

def add_lt_add [IsAddCancel β] (a b c d: β) : a < c -> b < d -> a + b < c + d := by
  intro ac bd
  apply lt_trans
  apply add_lt_add_left
  assumption
  apply add_lt_add_right
  assumption

def add_lt_add_of_lt_of_le [IsAddLeftCancel β] (a b c d: β) : a < c -> b ≤ d -> a + b < c + d := by
  intro ac bd
  apply lt_of_lt_of_le
  apply add_lt_add_right
  assumption
  apply add_le_add_left
  assumption

def add_lt_add_of_le_of_lt [IsAddRightCancel β] (a b c d: β) : a ≤ c -> b < d -> a + b < c + d := by
  intro ac bd
  apply lt_of_le_of_lt
  apply add_le_add_right
  assumption
  apply add_lt_add_left
  assumption

end

section

variable [IsMonoid α] [IsOrderedCommMonoid β] [AbsoluteValue α β] [IsOrderedAbsMonoid α]

def mul_lt_mul_left [IsLeftCancel β] (a b k: β) : a < b -> k * a < k * b := by
  intro h
  apply lt_of_le_of_ne
  apply mul_le_mul_left
  apply le_of_lt; assumption
  intro g
  rw [mul_left_cancel g] at h
  exact lt_irrefl h

def mul_lt_mul_right [IsRightCancel β] (a b k: β) : a < b -> a * k < b * k := by
  intro h
  apply lt_of_le_of_ne
  apply mul_le_mul_right
  apply le_of_lt; assumption
  intro g
  rw [mul_right_cancel g] at h
  exact lt_irrefl h

def mul_lt_mul [IsMulCancel β] (a b c d: β) : a < c -> b < d -> a * b < c * d := by
  intro ac bd
  apply lt_trans
  apply mul_lt_mul_left
  assumption
  apply mul_lt_mul_right
  assumption

def mul_lt_mul_of_lt_of_le [IsLeftCancel β] (a b c d: β) : a < c -> b ≤ d -> a * b < c * d := by
  intro ac bd
  apply lt_of_lt_of_le
  apply mul_lt_mul_right
  assumption
  apply mul_le_mul_left
  assumption

def mul_lt_mul_of_le_of_lt [IsRightCancel β] (a b c d: β) : a ≤ c -> b < d -> a * b < c * d := by
  intro ac bd
  apply lt_of_le_of_lt
  apply mul_le_mul_right
  assumption
  apply mul_lt_mul_left
  assumption

end

section

variable [IsAddGroup α] [IsOrderedAddCommMonoid β] [AbsoluteValue α β] [IsOrderedAbsAddGroup α]

def abs_sub_comm (a b: α) : ‖a - b‖ = ‖b - a‖ := by
  rw [←neg_abs (a - b), neg_sub]

end

section

variable [IsMonoid α] [IsMonoid β] [AbsoluteValue α β] [IsOrderedAbsMonoid α]

def abs_pow (a: α) (n: ℕ) : ‖a ^ n‖ = ‖a‖ ^ n := by
  induction n with
  | zero => rw [npow_zero, npow_zero, abs_one]
  | succ n ih => rw [npow_succ, npow_succ, mul_abs, ih]

end

section

variable [IsSemiring α] [IsOrderedSemiring β] [AbsoluteValue α β] [IsOrderedAbsSemiring α]

end

section

variable [IsRing α] [IsOrderedSemiring β] [AbsoluteValue α β] [IsOrderedAbsRing α]

def zsmul_abs: ∀a: α, ∀n: Int, ‖n • a‖ = ‖n‖ • ‖a‖ := by
  intro a n
  show _ = Int.natAbs _ • _
  cases n with
  | ofNat n => erw [zsmul_ofNat, Int.natAbs_ofNat, nsmul_abs]
  | negSucc n => erw [Int.negSucc_eq, neg_zsmul, neg_abs, Int.natAbs_neg,
      ←Int.ofNat_add, Int.natAbs_ofNat, zsmul_ofNat, nsmul_abs]

variable [IsNontrivial β] [IsAddRightCancel β]

def two_pos [IsNontrivial β] [IsAddRightCancel β] : 0 < (2: β) := by
  apply lt_trans
  exact zero_lt_one
  have : 1 + 1 = (2: β) := by
    rw [ofNat_eq_natCast, natCast_succ, natCast_succ, natCast_zero, zero_add]
  rw [←add_zero 1, ←this]; clear this
  apply add_lt_add_of_le_of_lt
  rfl
  exact zero_lt_one

def zero_ne_two : (2: β) ≠ 0 := (ne_of_lt two_pos).symm

variable
 [Sub β] [Pow β ℤ] [SMul ℤ β] [Neg β] [IntCast β] [CheckedInvert β (· ≠ 0)] [CheckedDiv β (· ≠ 0)] [IsField β]
 [IsField β] [IsOrderedCommMonoid β]

def half_pos {ε: β} (h: 0 < ε) : 0 < ε /? 2 ~(zero_ne_two) := by
  rw [div_eq_mul_inv?]
  apply lt_of_le_of_ne
  conv => { lhs; rw [←mul_zero 0] }
  apply mul_le_mul
  apply le_of_lt; assumption
  ·
    sorry
  intro eq
  have : 0 * 2 = (ε * 2⁻¹?~(zero_ne_two)) * 2 := by rw [←eq]
  rw [mul_assoc, zero_mul, mul_comm _ 2, mul_inv?_cancel, mul_one] at this
  subst ε
  have := lt_irrefl h
  contradiction

end
