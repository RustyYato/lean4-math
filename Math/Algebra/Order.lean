import Math.Algebra.Field.Basic
import Math.Order.Linear
import Math.Ops.Abs
import Math.Ops.CheckedOrder

variable [LT α] [LE α] [LT β] [LE β]

class IsOrderedAddCommMonoid (α: Type*) [AddMonoidOps α] [LT α] [LE α] : Prop extends IsAddCommMagma α, IsAddMonoid α, IsPartialOrder α  where
  add_le_add_left : ∀ a b : α, a ≤ b → ∀ c, c + a ≤ c + b
  le_iff_nsmul_le: ∀a b: α, ∀n > 0, a ≤ b ↔ n • a ≤ n • b

class IsOrderedCommMonoid (α: Type*) [MonoidOps α] [LT α] [LE α] : Prop extends IsCommMagma α, IsMonoid α, IsPartialOrder α  where
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
  mul_nonneg: ∀a b: α, 0 ≤ a -> 0 ≤ b -> 0 ≤ a * b
  mul_le_mul_of_nonneg_left: ∀a b: α, a ≤ b -> ∀c, 0 ≤ c -> c * a ≤ c * b
  mul_le_mul_of_nonneg_right: ∀a b: α, a ≤ b -> ∀c, 0 ≤ c -> a * c ≤ b * c

export IsOrderedSemiring (zero_le_one mul_le_mul_of_nonneg_left mul_le_mul_of_nonneg_right)

def zero_lt_one [SemiringOps α] [IsOrderedSemiring α] [IsNontrivial α] : (0: α) < 1 := lt_of_le_of_ne zero_le_one (zero_ne_one _)

class IsOrderedRing (α: Type*) [RingOps α] [LT α] [LE α] extends IsRing α, IsOrderedSemiring α where

class IsStrictOrderedSemiring (α: Type*) [SemiringOps α] [LT α] [LE α] extends IsSemiring α, IsOrderedSemiring α, IsNontrivial α where
  mul_pos: ∀a b: α, 0 < a -> 0 < b -> 0 < a * b

class IsStrictOrderedRing (α: Type*) [RingOps α] [LT α] [LE α] extends IsRing α, IsOrderedRing α, IsStrictOrderedSemiring α where

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

instance : IsOrderedAddCommMonoid ℤ where
  add_le_add_left := by
    intro a b h c
    apply Int.add_le_add_left
    assumption
  le_iff_nsmul_le := by
    intro a b n h
    apply Iff.intro
    show a ≤ b -> n * a ≤ n * b
    intro h
    apply Int.mul_le_mul_of_nonneg_left
    exact h
    exact Int.ofNat_zero_le n
    intro h
    apply Int.le_of_mul_le_mul_left
    assumption
    apply Int.ofNat_pos.mpr
    assumption

section

variable [AddMonoidOps α] [AddMonoidOps β] [IsAddMonoid α] [IsOrderedAddCommMonoid β] [AbsoluteValue α β] [IsOrderedAbsAddMonoid α]

def nsmul_le : ∀a b: β, ∀n: ℕ, a ≤ b -> n • a ≤ n • b := by
  intro a b n h
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul]
  | succ n ih =>
    rw [succ_nsmul, succ_nsmul]
    apply add_le_add
    assumption
    assumption

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

def le_iff_nsmul_le [IsAddCancel β]: ∀a b: β, ∀n > 0, a ≤ b ↔ n • a ≤ n • b := by
  intro a b n h
  cases n with
  | zero => contradiction
  | succ n =>
  clear h
  rw [succ_nsmul, succ_nsmul]
  apply Iff.intro
  intro h
  apply add_le_add
  apply nsmul_le
  assumption
  assumption
  intro h
  sorry

end

section

variable [AddGroupOps α] [IsAddGroup α] [IsOrderedAddCommMonoid α]

local instance : IsLawfulLT α := (inferInstanceAs (IsOrderedAddCommMonoid α)).toIsLawfulLT

def neg_le_neg_iff (a b: α) : -a ≤ -b ↔ b ≤ a := by
  revert a b
  suffices ∀a b: α, a ≤ b -> -b ≤ -a by
    intro a b
    apply Iff.intro _ (this _ _)
    intro h
    have := this _ _ h
    rw [neg_neg, neg_neg] at this
    assumption
  intro a b h
  have := add_le_add_left _ _ h (-a)
  rw [neg_add_cancel] at this
  have := add_le_add_right _ _ this (-b)
  rw [zero_add, add_assoc, add_neg_cancel, add_zero] at this
  assumption

def add_le_add_iff_left {a b k: α} : a ≤ b ↔ k + a ≤ k + b := by
  apply Iff.intro
  intro
  apply add_le_add_left
  assumption
  intro h
  have := add_le_add_left _ _ h (-k)
  rw [←add_assoc, ←add_assoc, neg_add_cancel, zero_add, zero_add] at this
  assumption

def add_le_add_iff_right {a b k: α} : a ≤ b ↔ a + k ≤ b + k := by
  apply Iff.intro
  intro
  apply add_le_add_right
  assumption
  intro h
  have := add_le_add_right _ _ h (-k)
  rw [add_assoc, add_assoc, add_neg_cancel, add_zero, add_zero] at this
  assumption

def add_lt_add_iff_left {a b k: α} : a < b ↔ k + a < k + b := by
  simp [lt_iff_le_and_not_le, ←add_le_add_iff_left]

def add_lt_add_iff_right {a b k: α} : a < b ↔ a + k < b + k := by
  simp [lt_iff_le_and_not_le, ←add_le_add_iff_right]

def add_le_iff_le_sub {a b k: α} : a + k ≤ b ↔ a ≤ b - k := by
  rw [add_le_add_iff_right (k := -k), add_assoc, add_neg_cancel, add_zero, sub_eq_add_neg]
def le_add_iff_sub_le {a b k: α} : a ≤ b + k ↔ a - k ≤ b := by
  rw [add_le_add_iff_right (k := -k), add_assoc, add_neg_cancel, add_zero, sub_eq_add_neg]

def add_lt_iff_lt_sub {a b k: α} : a + k < b ↔ a < b - k := by
  simp [lt_iff_le_and_not_le, add_le_iff_le_sub, le_add_iff_sub_le]

def lt_add_iff_sub_lt {a b k: α} : a < b + k ↔ a - k < b := by
  simp [lt_iff_le_and_not_le, add_le_iff_le_sub, le_add_iff_sub_le]

end

section

variable [MonoidOps α] [MonoidOps β] [IsMonoid α] [IsOrderedCommMonoid β]

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

variable [SemiringOps α] [IsOrderedSemiring α] [IsNontrivial α]

def le_succ_self (a: α) : a ≤ a + 1 := by
  rw (occs := [1]) [←add_zero a]
  apply add_le_add_left
  apply zero_le_one

end

section

variable [RingOps α] [IsOrderedRing α] [IsNontrivial α]

local instance : IsPartialOrder α :=
  (inferInstanceAs (IsOrderedRing α)).toIsPartialOrder
local instance : IsLawfulLT α :=
  (inferInstanceAs (IsOrderedRing α)).toIsLawfulLT

@[norm_cast]
def le_iff_natCast_le {n m: ℕ} : n ≤ (m: α) ↔ n ≤ m := by
  induction n generalizing m with
  | zero =>
    simp [natCast_zero]
    induction m with
    | zero => rw [natCast_zero]
    | succ m ih =>
      rw [natCast_add]
      rw [←add_zero 0]
      apply add_le_add
      assumption
      rw [natCast_one]
      apply zero_le_one
  | succ n ih =>
    cases m with
    | zero =>
      simp [natCast_succ]
      intro h
      cases Nat.le_zero.mp <| ih.mp <| le_trans (le_succ_self (n: α)) h
      simp [natCast_zero] at h
      exact not_lt_of_le h zero_lt_one
    | succ m =>
      simp [natCast_succ]
      rw [←ih]
      apply Iff.intro
      intro h
      have := add_le_add_right _ _ h (-1)
      rw [add_assoc, add_assoc, add_neg_cancel] at this
      simpa [this]
      intro h
      apply add_le_add_right
      assumption

@[norm_cast]
def le_iff_intCast_le {n m: ℤ} : n ≤ (m: α) ↔ n ≤ m := by
  cases n <;> cases m <;> rename_i n m
  norm_cast
  apply le_iff_natCast_le
  · apply flip Iff.intro
    intro h
    have := lt_of_le_of_lt h (Int.negSucc_lt_zero m)
    contradiction
    norm_cast
    rw [intCast_negSucc]
    intro h
    have := add_le_add_right _ _ h (m.succ)
    rw [neg_add_cancel, ←natCast_add, ←natCast_zero] at this
    norm_cast at this
  · apply Iff.intro
    intro h
    apply le_trans
    apply le_of_lt
    apply Int.negSucc_lt_zero
    apply Int.ofNat_zero_le
    intro
    norm_cast
    rw [intCast_negSucc]
    have := add_le_add_right 0 (m + n.succ: α) ?_ (-n.succ)
    rw [zero_add, add_assoc, add_neg_cancel, add_zero] at this
    assumption
    rw [←natCast_add, ←natCast_zero]
    apply le_iff_natCast_le.mpr
    apply Nat.zero_le
  · rw [intCast_negSucc, intCast_negSucc, neg_le_neg_iff,
      Int.negSucc_eq, Int.negSucc_eq, neg_le_neg_iff,
      ←natCast_succ, ←natCast_succ, Int.ofNat_le]
    apply le_iff_natCast_le

@[norm_cast]
def lt_iff_natCast_lt {n m: ℕ} : n < (m: α) ↔ n < m := by
  iterate 2 rw [lt_iff_le_and_not_le]
  iterate 2 rw [le_iff_natCast_le]

@[norm_cast]
def lt_iff_intCast_lt {n m: ℤ} : n < (m: α) ↔ n < m := by
  iterate 2 rw [lt_iff_le_and_not_le]
  iterate 2 rw [le_iff_intCast_le]

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

def two_pos : 0 < (2: α) := by
  show (0: α) < OfNat.ofNat (0 + 2)
  have := ofNat_eq_natCast (α := α) 0
  rw [ofNat_eq_natCast (α := α) 0, Nat.zero_add, show 2 = 1 + 1 by rfl, natCast_add]
  apply lt_of_lt_of_le
  apply zero_lt_one
  rw [←add_zero (1: α), natCast_one]
  apply add_le_add_left
  apply zero_le_one

def add_half (a: α) : a /? 2 ~(by symm; apply ne_of_lt two_pos) + a /? 2 ~(by symm; apply ne_of_lt two_pos) = a := by
  rw [add_div?_add', ←mul_two, div?_eq_mul_inv?, mul_assoc, mul_inv?_cancel, mul_one]

section

variable [IsLinearOrder α]

def inv?_pos (a: α) (h: 0 < a): 0 < a⁻¹? := by
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

def div?_pos (a b: α) (ha: 0 < a) (hb: 0 < b): 0 < a /? b := by
  rw [div?_eq_mul_inv?]; conv => { lhs; rw [←mul_zero a] }
  apply mul_lt_mul_of_pos_left
  apply inv?_pos
  assumption
  assumption

def half_pos {ε: α} (h: 0 < ε) : 0 < ε /? 2 ~(((ne_of_lt two_pos).symm: (2: α) ≠ 0)) := by
  have := mul_lt_mul_of_pos_left _ _ (inv?_pos _ two_pos) _ h
  rw [mul_zero, ←div?_eq_mul_inv?] at this
  assumption

def lt_iff_mul_lt_mul_of_pos_right (a b k: α) (h: 0 < k) : a < b ↔ a * k < b * k := by
  revert a b k
  suffices ∀(a b k : α), 0 < k → a < b -> a * k < b * k by
    intro a b k kpos
    apply Iff.intro
    apply this
    assumption
    intro h
    have := this _ _ k⁻¹? (inv?_pos _ kpos) h
    rw [mul_assoc, mul_assoc, mul_inv?_cancel, mul_one, mul_one] at this
    assumption
  intro a b k kpos altb
  apply mul_lt_mul_of_pos_right
  assumption
  assumption

def lt_iff_mul_lt_mul_of_pos_left (a b k: α) (h: 0 < k) : a < b ↔ k * a < k * b := by
  revert a b k
  suffices ∀(a b k : α), 0 < k → a < b -> k * a < k * b by
    intro a b k kpos
    apply Iff.intro
    apply this
    assumption
    intro h
    have := this _ _ k⁻¹? (inv?_pos _ kpos) h
    rw [←mul_assoc, ←mul_assoc, inv?_mul_cancel, one_mul, one_mul] at this
    assumption
  intro a b k kpos altb
  apply mul_lt_mul_of_pos_left
  assumption
  assumption

def le_iff_mul_le_mul_of_pos_right (a b k: α) (h: 0 < k) : a ≤ b ↔ a * k ≤ b * k := by
  apply le_iff_of_lt_iff
  apply lt_iff_mul_lt_mul_of_pos_right
  assumption

def le_iff_mul_le_mul_of_pos_left (a b k: α) (h: 0 < k) : a ≤ b ↔ k * a ≤ k * b := by
  apply le_iff_of_lt_iff
  apply lt_iff_mul_lt_mul_of_pos_left
  assumption

end

section

variable [Min α] [Max α] [IsLinearMinMaxOrder α] [NeZero (2: α)]

local instance : IsLinearOrder α :=
  (inferInstanceAs (IsLinearMinMaxOrder α)).toIsLinearOrder

def min_le_midpoint (a b: α) : min a b ≤ midpoint a b := by
  apply min_le_iff.mpr
  unfold midpoint
  rcases lt_or_le a b
  left; apply (le_iff_mul_le_mul_of_pos_right _ _ 2 _).mpr
  rw [div?_mul_cancel, mul_two]
  apply add_le_add_left
  apply le_of_lt; assumption
  apply two_pos
  right; apply (le_iff_mul_le_mul_of_pos_right _ _ 2 _).mpr
  rw [div?_mul_cancel, mul_two]
  apply add_le_add_right
  assumption
  exact two_pos

def midpoint_le_max (a b: α) : midpoint a b ≤ max a b := by
  apply le_max_iff.mpr
  unfold midpoint
  rcases lt_or_le b a
  left; apply (le_iff_mul_le_mul_of_pos_right _ _ 2 _).mpr
  rw [div?_mul_cancel, mul_two]
  apply add_le_add_left
  apply le_of_lt; assumption
  apply two_pos
  right; apply (le_iff_mul_le_mul_of_pos_right _ _ 2 _).mpr
  rw [div?_mul_cancel, mul_two]
  apply add_le_add_right
  assumption
  apply two_pos

def inv?_lt_inv? [IsCommMagma α] (a b: α) (ha: 0 < a) (hb: 0 < b) : a⁻¹? < b⁻¹? ↔ b < a := by
  revert a b
  suffices ∀(a b: α) (ha: 0 < a) (hb: 0 < b), a < b -> b⁻¹? < a⁻¹? by
    intro a b ha hb
    apply flip Iff.intro
    apply this
    assumption
    assumption
    intro h
    have := this _ _ ?_ ?_ h
    rw [inv?_inv?, inv?_inv?] at this
    assumption
    apply inv?_pos
    assumption
    apply inv?_pos
    assumption
  intro a b ha hb h
  have := mul_lt_mul_of_pos_left _ _ h (a⁻¹? * b⁻¹?) ?_
  rw [mul_assoc _ _ b, mul_comm (a⁻¹?), mul_assoc, inv?_mul_cancel,
    inv?_mul_cancel, mul_one, mul_one] at this
  assumption
  rw (occs := [1]) [←zero_mul (b⁻¹?)]
  apply mul_lt_mul_of_pos_right
  apply inv?_pos; assumption
  apply inv?_pos; assumption

end

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
