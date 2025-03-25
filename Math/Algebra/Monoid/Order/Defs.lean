import Math.Algebra.Monoid.Defs
import Math.Algebra.AddMul.Order
import Math.Order.Monotone.Defs

variable [LT α] [LE α] [LT α] [LE α]

class IsZeroLeOne (α: Type*) [Zero α] [One α] [LE α] where
  zero_le_one: 0 ≤ (1: α)

class IsOrderedAddCommMonoid (α: Type*) [AddMonoidOps α] [LT α] [LE α] : Prop extends IsAddCommMagma α, IsAddMonoid α, IsPartialOrder α  where
  protected add_le_add_left: ∀a b : α, a ≤ b → ∀ c, c + a ≤ c + b

class IsOrderedCommMonoid (α: Type*) [MonoidOps α] [LT α] [LE α] : Prop extends IsCommMagma α, IsMonoid α, IsPartialOrder α  where
  protected mul_le_mul_left: ∀a b : α, a ≤ b → ∀ c, c * a ≤ c * b

class IsOrderedCancelAddCommMonoid (α: Type*) [AddMonoidOps α] [LT α] [LE α] extends IsOrderedAddCommMonoid α, IsAddCancel α where
  protected le_of_add_le_add_left: ∀a b c: α, a + b ≤ a + c → b ≤ c

class IsOrderedCancelCommMonoid (α: Type*) [MonoidOps α] [LT α] [LE α] extends IsOrderedCommMonoid α, IsMulCancel α where
  protected le_of_mul_le_mul_left: ∀a b c: α, a * b ≤ a * c → b ≤ c

instance [MonoidOps α] [IsOrderedCommMonoid α] : IsOrderedAddCommMonoid (AddOfMul α) where
  add_le_add_left := IsOrderedCommMonoid.mul_le_mul_left (α := α)
instance [AddMonoidOps α] [IsOrderedAddCommMonoid α] : IsOrderedCommMonoid (MulOfAdd α) where
  mul_le_mul_left := IsOrderedAddCommMonoid.add_le_add_left (α := α)

instance [MonoidOps α] [IsOrderedCancelCommMonoid α] : IsOrderedCancelAddCommMonoid (AddOfMul α) where
  le_of_add_le_add_left := IsOrderedCancelCommMonoid.le_of_mul_le_mul_left (α := α)
instance [AddMonoidOps α] [IsOrderedCancelAddCommMonoid α] : IsOrderedCancelCommMonoid (MulOfAdd α) where
  le_of_mul_le_mul_left := IsOrderedCancelAddCommMonoid.le_of_add_le_add_left (α := α)

def zero_le_one [Zero α] [One α] [IsZeroLeOne α] : (0: α) ≤ 1 := IsZeroLeOne.zero_le_one

def zero_lt_one [Zero α] [One α] [Mul α] [IsMulZeroClass α] [IsMulOneClass α] [IsZeroLeOne α] [IsNontrivial α] [IsPartialOrder α] : (0: α) < 1 := by
  apply lt_of_le_of_ne
  apply zero_le_one
  apply zero_ne_one

section IsOrderedAddCommMonoid

variable [AddMonoidOps α] [IsOrderedAddCommMonoid α]

def add_le_add_left : ∀a b : α, a ≤ b → ∀ c, c + a ≤ c + b := IsOrderedAddCommMonoid.add_le_add_left

def add_le_add_right (a b: α) : a ≤ b -> ∀c, a + c ≤ b + c := by
  intro h c
  rw [add_comm _ c, add_comm _ c]
  apply add_le_add_left
  assumption

def add_le_add (a b c d: α) : a ≤ c -> b ≤ d -> a + b ≤ c + d := by
  intro ac bd
  apply le_trans
  apply add_le_add_left
  assumption
  apply add_le_add_right
  assumption

def nsmul_le_nsmul (a b: α) (n: ℕ) : a ≤ b -> n • a ≤ n • b := by
  intro h
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul]
  | succ n ih =>
    rw [succ_nsmul, succ_nsmul]
    apply add_le_add
    assumption
    assumption

def add_lt_add_left [IsAddLeftCancel α] (a b k: α) : a < b -> k + a < k + b := by
  intro h
  apply lt_of_le_of_ne
  apply add_le_add_left
  apply le_of_lt; assumption
  intro g
  rw [add_left_cancel g] at h
  exact lt_irrefl h

def add_lt_add_right [IsAddRightCancel α] (a b k: α) : a < b -> a + k < b + k := by
  intro h
  apply lt_of_le_of_ne
  apply add_le_add_right
  apply le_of_lt; assumption
  intro g
  rw [add_right_cancel g] at h
  exact lt_irrefl h

def add_lt_add [IsAddCancel α] (a b c d: α) : a < c -> b < d -> a + b < c + d := by
  intro ac bd
  apply lt_trans
  apply add_lt_add_left
  assumption
  apply add_lt_add_right
  assumption

def add_lt_add_of_lt_of_le [IsAddLeftCancel α] (a b c d: α) : a < c -> b ≤ d -> a + b < c + d := by
  intro ac bd
  apply lt_of_lt_of_le
  apply add_lt_add_right
  assumption
  apply add_le_add_left
  assumption

def add_lt_add_of_le_of_lt [IsAddRightCancel α] (a b c d: α) : a ≤ c -> b < d -> a + b < c + d := by
  intro ac bd
  apply lt_of_le_of_lt
  apply add_le_add_right
  assumption
  apply add_lt_add_left
  assumption

def le_add_left (a b: α) (h: 0 ≤ b) : a ≤ b + a := by
  rw (occs := [1]) [←zero_add a]
  apply add_le_add_right
  assumption

def le_add_right (a b: α) (h: 0 ≤ b) : a ≤ a + b := by
  rw (occs := [1]) [←add_zero a]
  apply add_le_add_left
  assumption

end IsOrderedAddCommMonoid

section IsOrderedCancelAddCommMonoid

variable [AddMonoidOps α] [IsOrderedCancelAddCommMonoid α]

def le_of_add_le_add_left: ∀a b c: α, a + b ≤ a + c → b ≤ c :=
  IsOrderedCancelAddCommMonoid.le_of_add_le_add_left
def le_of_add_le_add_right: ∀a b c: α, a + c ≤ b + c → a ≤ b := by
  intro a b c
  rw [add_comm _ c, add_comm _ c]
  apply le_of_add_le_add_left

end IsOrderedCancelAddCommMonoid

section IsLinearOrderedAddCommMonoid

variable [IsLinearOrder α] [AddMonoidOps α] [IsOrderedAddCommMonoid α] [IsAddCancel α]

def nmsul_strict_mono (n: ℕ) (h: 0 < n) : StrictMonotone (α := α) (n • ·) := by
  intro a b g
  simp
  cases n with
  | zero => contradiction
  | succ n =>
  rw [succ_nsmul, succ_nsmul]
  apply add_lt_add_of_le_of_lt
  apply nsmul_le_nsmul
  apply le_of_lt
  assumption
  assumption

def le_of_nsmul_le_nsmul (a b: α) (n: ℕ) (h: 0 < n) : n • a ≤ n • b -> a ≤ b :=
  (nmsul_strict_mono n h).le_iff_le.mp

end IsLinearOrderedAddCommMonoid

section IsOrderedCommMonoid

variable [MonoidOps α] [IsOrderedCommMonoid α]

def mul_le_mul_left : ∀a b : α, a ≤ b → ∀ c, c * a ≤ c * b := IsOrderedCommMonoid.mul_le_mul_left

def mul_le_mul_right (a b: α) : a ≤ b -> ∀c, a * c ≤ b * c :=
  add_le_add_right (α := AddOfMul α) _ _

def mul_le_mul (a b c d: α) : a ≤ c -> b ≤ d -> a * b ≤ c * d :=
  add_le_add (α := AddOfMul α) _ _ _ _

def npow_le_npow (a b: α) (n: ℕ) : a ≤ b -> a ^ n ≤ b ^ n :=
  nsmul_le_nsmul (α := AddOfMul α) _ _ _

def mul_lt_mul_left [IsLeftCancel α] (a b k: α) : a < b -> k * a < k * b :=
  add_lt_add_left (α := AddOfMul α) _ _ _

def mul_lt_mul_right [IsRightCancel α] (a b k: α) : a < b -> a * k < b * k :=
  add_lt_add_right (α := AddOfMul α) _ _ _

def mul_lt_mul [IsMulCancel α] (a b c d: α) : a < c -> b < d -> a * b < c * d :=
  add_lt_add (α := AddOfMul α) _ _ _ _

def mul_lt_mul_of_lt_of_le [IsLeftCancel α] (a b c d: α) : a < c -> b ≤ d -> a * b < c * d :=
  add_lt_add_of_lt_of_le (α := AddOfMul α) _ _ _ _

def mul_lt_mul_of_le_of_lt [IsRightCancel α] (a b c d: α) : a ≤ c -> b < d -> a * b < c * d :=
  add_lt_add_of_le_of_lt (α := AddOfMul α) _ _ _ _

end IsOrderedCommMonoid

section IsOrderedCancelCommMonoid

variable [MonoidOps α] [IsOrderedCancelCommMonoid α]

def le_of_mul_le_mul_left: ∀a b c: α, a * b ≤ a * c → b ≤ c :=
  IsOrderedCancelCommMonoid.le_of_mul_le_mul_left
def le_of_mul_le_mul_right: ∀a b c: α, a * c ≤ b * c → a ≤ b :=
  le_of_add_le_add_right (α := AddOfMul α)

end IsOrderedCancelCommMonoid

section IsLinearOrderedCommMonoid

variable [IsLinearOrder α] [MonoidOps α] [IsOrderedCommMonoid α] [IsMulCancel α]

def pow_strict_mono (n: ℕ) (h: 0 < n) : StrictMonotone (α := α) (· ^ n) :=
  nmsul_strict_mono (α := AddOfMul α) _ h

def le_of_npow_le_npow (a b: α) (n: ℕ) (h: 0 < n) : a ^ n ≤ b ^ n -> a ≤ b :=
  (pow_strict_mono n h).le_iff_le.mp

end IsLinearOrderedCommMonoid
