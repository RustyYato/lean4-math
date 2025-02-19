import Math.Algebra.Ring
import Math.Order.Linear
import Math.Ops.Abs
import Math.Ops.CheckedOrder

variable [LT α] [LE α] [LT β] [LE β]

class IsOrderedAddCommMonoid (α: Type*) [AddMonoidOps α] [LT α] [LE α] extends IsAddCommMagma α, IsAddMonoid α, IsPartialOrder α : Prop where
  add_le_add_left : ∀ a b : α, a ≤ b → ∀ c, c + a ≤ c + b
  le_iff_nsmul_le: ∀a b: α, ∀n > 0, a ≤ b ↔ n • a ≤ n • b

class IsOrderedCommMonoid (α: Type*) [MonoidOps α] [LT α] [LE α] extends IsCommMagma α, IsMonoid α, IsPartialOrder α : Prop where
  mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c, c * a ≤ c * b

export IsOrderedAddCommMonoid (
  le_iff_nsmul_le
)

def add_le_add_left [AddMonoidOps α] [IsOrderedAddCommMonoid α] : ∀ a b : α, a ≤ b → ∀ c, c + a ≤ c + b := IsOrderedAddCommMonoid.add_le_add_left
def add_le_add_right [AddMonoidOps α] [IsOrderedAddCommMonoid α] : ∀ a b : α, a ≤ b → ∀ c, a + c ≤ b + c := by
  intro a b a_le_b c
  rw [add_comm _ c, add_comm _ c]
  apply add_le_add_left
  assumption

def add_le_add [AddMonoidOps α] [IsOrderedAddCommMonoid α] : ∀a b c d: α, a ≤ c -> b ≤ d -> a + b ≤ c + d := by
  intro a b c d ac bd
  apply le_trans
  apply add_le_add_left
  assumption
  apply add_le_add_right
  assumption

def mul_le_mul_left [MonoidOps α] [IsOrderedCommMonoid α] : ∀ a b : α, a ≤ b → ∀ c, c * a ≤ c * b := IsOrderedCommMonoid.mul_le_mul_left
def mul_le_mul_right [MonoidOps α] [IsOrderedCommMonoid α] : ∀ a b : α, a ≤ b → ∀ c, a * c ≤ b * c := by
  intro a b a_le_b c
  rw [mul_comm _ c, mul_comm _ c]
  apply mul_le_mul_left
  assumption

def mul_le_mul [MonoidOps α] [IsOrderedCommMonoid α] : ∀a b c d: α, a ≤ c -> b ≤ d -> a * b ≤ c * d := by
  intro a b c d ac bd
  apply le_trans
  apply mul_le_mul_left
  assumption
  apply mul_le_mul_right
  assumption

class IsOrderedSemiring (α: Type*) [SemiringOps α] [LT α] [LE α] extends IsSemiring α, IsOrderedAddCommMonoid α where
  zero_le_one: 0 ≤ (1: α)
  mul_le_mul_of_nonneg_left: ∀a b: α, a ≤ b -> ∀c, 0 ≤ c -> c * a ≤ c * b
  mul_le_mul_of_nonneg_right: ∀a b: α, a ≤ b -> ∀c, 0 ≤ c -> a * c ≤ b * c

export IsOrderedSemiring (zero_le_one mul_le_mul_of_nonneg_left mul_le_mul_of_nonneg_right)

def zero_lt_one [SemiringOps α] [IsOrderedSemiring α] [IsNontrivial α] : (0: α) < 1 := lt_of_le_of_ne zero_le_one (zero_ne_one _)

class IsOrderedRing (α: Type*) [RingOps α] [LT α] [LE α] extends IsRing α, IsOrderedSemiring α where
  mul_nonneg: ∀a b: α, 0 ≤ a -> 0 ≤ b -> 0 ≤ a * b

class IsStrictOrderedRing (α: Type*) [RingOps α] [LT α] [LE α] extends IsRing α, IsOrderedRing α, IsNontrivial α where
  mul_pos: ∀a b: α, 0 < a -> 0 < b -> 0 < a * b

class IsLawfulAbs (α: Type*) {β: outParam Type*}  [AbsoluteValue α β] [LT β] [LE β] [Zero β] extends IsLinearOrder β where
  abs_nonneg: ∀a: α, 0 ≤ ‖a‖

class IsOrderedAbsAddMonoid (α: Type*) {β: outParam Type*} [AddMonoidOps α] [AddMonoidOps β] [LT β] [LE β] [AbsoluteValue α β] [IsOrderedAddCommMonoid β] extends IsLawfulAbs α, IsAddMonoid α where
  abs_zero: ∀{x: α}, ‖x‖ = 0 ↔ x = 0
  abs_add_le_add_abs: ∀a b: α, ‖a + b‖ ≤ ‖a‖ + ‖b‖
  nsmul_abs: ∀a: α, ∀n: Nat, ‖n • a‖ = n • ‖a‖

class IsOrderedAbsMonoid (α: Type*) {β: outParam Type*} [MonoidOps α] [MonoidOps β] [LT β] [LE β] [AbsoluteValue α β] [Zero β] extends IsLawfulAbs α where
  abs_one: ‖(1: α)‖ = 1
  mul_abs: ∀a b: α, ‖a * b‖ = ‖a‖ * ‖b‖

export IsOrderedAbsAddMonoid (abs_zero abs_add_le_add_abs nsmul_abs)

export IsOrderedAbsMonoid (abs_one mul_abs)

class IsOrderedAbsAddGroup (α: Type*) {β: outParam Type*} [AddGroupOps α] [AddMonoidOps β] [LT β] [LE β] [IsAddGroup α] [IsOrderedAddCommMonoid β] [AbsoluteValue α β] extends IsAddGroup α, IsOrderedAbsAddMonoid α where
  neg_abs: ∀a: α, ‖-a‖ = ‖a‖

export IsOrderedAbsAddGroup (neg_abs)

class IsOrderedAbsAddMonoidWithOne (α: Type*) {β: outParam Type*} [AddMonoidWithOneOps α] [AddMonoidWithOneOps β] [LT β] [LE β] [IsAddMonoidWithOne α] [IsAddMonoidWithOne β] [IsOrderedAddCommMonoid β] [AbsoluteValue α β] extends IsOrderedAbsAddMonoid α where
  natcast_abs: ∀n: Nat, ‖(n: α)‖ = n

export IsOrderedAbsAddMonoidWithOne (natcast_abs)

class IsOrderedAbsAddGroupWithOne (α: Type*) {β: outParam Type*} [AddGroupWithOneOps α] [AddMonoidWithOneOps β] [LT β] [LE β] [IsAddGroupWithOne α] [IsAddMonoidWithOne β] [IsOrderedAddCommMonoid β] [AbsoluteValue α β] extends IsOrderedAbsAddMonoidWithOne α, IsOrderedAbsAddGroup α where
  intcast_abs: ∀n: Int, ‖(n: α)‖ = ‖n‖

export IsOrderedAbsAddGroupWithOne (intcast_abs)

class IsOrderedAbsSemiring (α: Type*) {β: outParam Type*} [SemiringOps α] [SemiringOps β] [LT β] [LE β] [IsSemiring α] [IsSemiring β] [IsOrderedAddCommMonoid β] [AbsoluteValue α β] extends IsOrderedAbsAddMonoidWithOne α, IsOrderedAbsMonoid α where

class IsOrderedAbsRing (α: Type*) {β: outParam Type*} [RingOps α] [SemiringOps β] [LT β] [LE β] [IsRing α] [IsSemiring β] [IsOrderedAddCommMonoid β] [AbsoluteValue α β] extends IsOrderedAbsAddGroupWithOne α, IsOrderedAbsSemiring α where

instance
  [SemiringOps α] [SemiringOps β] [LT β] [LE β] [IsSemiring α] [IsSemiring β] [IsOrderedAddCommMonoid β] [AbsoluteValue α β]
  [IsOrderedAbsAddMonoidWithOne α] [IsOrderedAbsMonoid α]
  : IsOrderedAbsSemiring α where
  abs_one := abs_one
  mul_abs := mul_abs

instance
  [RingOps α] [SemiringOps β] [LT β] [LE β] [IsRing α] [IsSemiring β] [IsOrderedAddCommMonoid β] [AbsoluteValue α β]
  [IsOrderedAbsAddGroupWithOne α] [IsOrderedAbsMonoid α]
  : IsOrderedAbsRing α where
  abs_one := abs_one
  mul_abs := mul_abs

section

variable [AddMonoidOps α] [AddMonoidOps β] [IsAddMonoid α] [IsOrderedAddCommMonoid β] [AbsoluteValue α β] [IsOrderedAbsAddMonoid α]

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

variable [MonoidOps α] [MonoidOps β] [IsMonoid α] [IsOrderedCommMonoid β] [AbsoluteValue α β] [Zero β] [IsOrderedAbsMonoid α]

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

variable [AddGroupOps α] [AddMonoidOps β] [IsAddGroup α] [IsOrderedAddCommMonoid β] [AbsoluteValue α β] [IsOrderedAbsAddGroup α]

def abs_sub_comm (a b: α) : ‖a - b‖ = ‖b - a‖ := by
  rw [←neg_abs (a - b), neg_sub]

end

section

variable [MonoidOps α] [MonoidOps β] [IsMonoid α] [IsMonoid β] [Zero β] [IsOrderedCommMonoid β] [AbsoluteValue α β] [IsOrderedAbsMonoid α]

def abs_pow (a: α) (n: ℕ) : ‖a ^ n‖ = ‖a‖ ^ n := by
  induction n with
  | zero => rw [npow_zero, npow_zero, abs_one]
  | succ n ih => rw [npow_succ, npow_succ, mul_abs, ih]

end

section

variable [AddGroupWithOneOps α] [AddMonoidWithOneOps β] [IsAddGroupWithOne α] [IsAddMonoidWithOne β] [IsOrderedAddCommMonoid β] [AbsoluteValue α β] [IsOrderedAbsAddGroupWithOne α]

def zsmul_abs: ∀a: α, ∀n: Int, ‖n • a‖ = ‖n‖ • ‖a‖ := by
  intro a n
  show _ = Int.natAbs _ • _
  cases n with
  | ofNat n => erw [zsmul_ofNat, Int.natAbs_ofNat, nsmul_abs]
  | negSucc n => erw [Int.negSucc_eq, neg_zsmul, neg_abs, Int.natAbs_neg,
      ←Int.ofNat_add, Int.natAbs_ofNat, zsmul_ofNat, nsmul_abs]

end

section

variable [FieldOps α] [IsNonCommField α] [IsOrderedSemiring α]

def mul_lt_mul_of_pos_left: ∀(a b : α), a < b → ∀ (c : α), 0 < c → c * a < c * b := by
  intro a b ab c cpos
  apply lt_of_le_of_ne
  apply mul_le_mul_of_nonneg_left
  apply le_of_lt
  assumption
  apply le_of_lt
  assumption
  intro h
  have : c ≠ 0 := by symm; apply ne_of_lt; assumption
  have : c⁻¹? * (c * a) = c⁻¹? * (c * b) := by rw [h]
  rw [←mul_assoc, ←mul_assoc, inv?_mul_cancel, one_mul, one_mul] at this
  subst b
  exact lt_irrefl ab

def mul_lt_mul_of_pos_right: ∀(a b : α), a < b → ∀ (c : α), 0 < c → a * c < b * c := by
  intro a b ab c cpos
  apply lt_of_le_of_ne
  apply mul_le_mul_of_nonneg_right
  apply le_of_lt
  assumption
  apply le_of_lt
  assumption
  intro h
  have : c ≠ 0 := by symm; apply ne_of_lt; assumption
  have : (a * c) * c⁻¹? = (b * c) * c⁻¹? := by rw [h]
  rw [mul_assoc, mul_assoc, mul_inv?_cancel, mul_one, mul_one] at this
  subst b
  exact lt_irrefl ab

def inv?_pos [IsLinearOrder α] (a: α) (h: 0 < a): 0 < a⁻¹? := by
  have anz : a ≠ 0 := by
    intro g; rw [g] at h
    exact lt_irrefl h
  apply lt_of_not_le
  intro g; replace g := lt_or_eq_of_le g
  cases g <;> rename_i g
  · have := mul_lt_mul_of_pos_left _ _ g _ h
    rw [mul_inv?_cancel, mul_zero] at this
    exact lt_irrefl (lt_trans this zero_lt_one)
  · have := mul_inv?_cancel a anz
    rw [g, mul_zero] at this
    exact zero_ne_one _ this

def div?_pos [IsLinearOrder α] (a b: α) (ha: 0 < a) (hb: 0 < b): 0 < a /? b := by
  rw [div?_eq_mul_inv?]; conv => { lhs; rw [←mul_zero a] }
  apply mul_lt_mul_of_pos_left
  apply inv?_pos
  assumption
  assumption

def two_pos : 0 < (2: α) := by
  show (0: α) < OfNat.ofNat (0 + 2)
  have := ofNat_eq_natCast (α := α) 0
  rw [ofNat_eq_natCast (α := α) 0, Nat.zero_add, show 2 = 1 + 1 by rfl, natCast_add]
  apply lt_of_lt_of_le
  apply zero_lt_one
  rw [←add_zero (1: α), natCast_one]
  apply add_le_add_left
  apply zero_le_one

def half_pos [IsLinearOrder α] {ε: α} (h: 0 < ε) : 0 < ε /? 2 ~(((ne_of_lt two_pos).symm: (2: α) ≠ 0)) := by
  have := mul_lt_mul_of_pos_left _ _ (inv?_pos _ two_pos) _ h
  rw [mul_zero, ←div?_eq_mul_inv?] at this
  assumption

def add_half (a: α) : a /? 2 ~(by symm; apply ne_of_lt two_pos) + a /? 2 ~(by symm; apply ne_of_lt two_pos) = a := by
  rw [add_div?_add', ←mul_two, div?_eq_mul_inv?, mul_assoc, mul_inv?_cancel, mul_one]

end

section

variable
  [AbsoluteValue α α]
  [AddGroupWithOneOps α] [IsAddGroupWithOne α]
  [LT α] [LE α] [IsOrderedAddCommMonoid α]
  [IsOrderedAbsAddGroupWithOne α]

-- open Classical in
-- def abs_lt_abs_iff {a b: α} :
--   ‖a‖ < ‖b‖ ↔ a < b ∧ 0 < a ∨ b < a ∧ a < 0 := by
--   apply Iff.intro
--   intro h
--   repeat sorry
--   have : ‖a‖ = if a < 0 then -a else a := by
--     split
--     rw [←neg_abs]
--     apply le_antisymm
--     sorry
--     apply
--     sorry
--     sorry


--   sorry

end

section
