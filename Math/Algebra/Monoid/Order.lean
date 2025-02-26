import Math.Algebra.Monoid.Defs
import Math.Algebra.AddMul.Order.Partial

variable [LT α] [LE α] [LT β] [LE β]

class ZeroLeOne (α: Type*) [Zero α] [One α] [LE α] where
  zero_le_one: 0 ≤ (1: α)

class IsOrderedAddCommMonoid (α: Type*) [AddMonoidOps α] [LT α] [LE α] : Prop extends IsAddCommMagma α, IsAddMonoid α, IsPartialOrder α  where
  protected add_le_add_left: ∀a b : α, a ≤ b → ∀ c, c + a ≤ c + b

class IsOrderedCommMonoid (α: Type*) [MonoidOps α] [LT α] [LE α] : Prop extends IsCommMagma α, IsMonoid α, IsPartialOrder α  where
  protected mul_le_mul_left: ∀a b : α, a ≤ b → ∀ c, c * a ≤ c * b

class IsOrderedCancelAddCommMonoid (α: Type*) [AddMonoidOps α] [LT α] [LE α] extends IsOrderedAddCommMonoid α where
  protected le_of_add_le_add_left: ∀a b c: α, a + b ≤ a + c → b ≤ c

class IsOrderedCancelCommMonoid (α: Type*) [MonoidOps α] [LT α] [LE α] extends IsOrderedCommMonoid α where
  protected le_of_mul_le_mul_left: ∀a b c: α, a * b ≤ a * c → b ≤ c

instance [MonoidOps α] [IsOrderedCommMonoid α] : IsOrderedAddCommMonoid (AddOfMul α) where
  add_le_add_left := IsOrderedCommMonoid.mul_le_mul_left (α := α)
instance [AddMonoidOps α] [IsOrderedAddCommMonoid α] : IsOrderedCommMonoid (MulOfAdd α) where
  mul_le_mul_left := IsOrderedAddCommMonoid.add_le_add_left (α := α)

section

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

def nsmul_le_nsmul (a b: α) (n: ℕ) :
  a ≤ b -> n • a ≤ n • b := by
  intro h
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul]
  | succ n ih =>
    rw [succ_nsmul, succ_nsmul]
    apply add_le_add
    assumption
    assumption

end

section

variable  [MonoidOps α] [IsOrderedCommMonoid α]

def mul_le_mul_left : ∀a b : α, a ≤ b → ∀ c, c * a ≤ c * b := IsOrderedCommMonoid.mul_le_mul_left

def mul_le_mul_right (a b: α) : a ≤ b -> ∀c, a * c ≤ b * c :=
  add_le_add_right (α := AddOfMul α) _ _

def mul_le_mul (a b c d: α) : a ≤ c -> b ≤ d -> a * b ≤ c * d :=
  add_le_add (α := AddOfMul α) _ _ _ _

def npow_le_npow (a b: α) (n: ℕ) :
  a ≤ b -> a ^ n ≤ b ^ n :=
  nsmul_le_nsmul (α := AddOfMul α) a b n

end
