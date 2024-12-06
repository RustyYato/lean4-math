import Math.Algebra.Ring
import Math.Order.Partial

variable (α: Type*) [LT α] [LE α] [Add α] [Zero α] [SMul ℕ α] [Mul α] [One α] [Pow α ℕ]

class IsOrderedAddCommMonoid extends IsAddCommMagma α, IsAddMonoid α, IsPartialOrder α : Prop where
  add_le_add_left : ∀ a b : α, a ≤ b → ∀ c, c + a ≤ c + b

class IsOrderedCommMonoid extends IsCommMagma α, IsMonoid α, IsPartialOrder α : Prop where
  mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c, c * a ≤ c * b

def add_le_add_left [IsOrderedAddCommMonoid α] : ∀ a b : α, a ≤ b → ∀ c, c + a ≤ c + b := IsOrderedAddCommMonoid.add_le_add_left
def add_le_add_right [IsOrderedAddCommMonoid α] : ∀ a b : α, a ≤ b → ∀ c, a + c ≤ b + c := by
  intro a b a_le_b c
  rw [add_comm _ c, add_comm _ c]
  apply add_le_add_left
  assumption

def add_le_add [IsOrderedAddCommMonoid α] : ∀a b c d: α, a ≤ c -> b ≤ d -> a + b ≤ c + d := by
  intro a b c d ac bd
  apply le_trans
  apply add_le_add_left
  assumption
  apply add_le_add_right
  assumption

def mul_le_mul_left  [IsOrderedCommMonoid α] : ∀ a b : α, a ≤ b → ∀ c, c * a ≤ c * b := IsOrderedCommMonoid.mul_le_mul_left
def mul_le_mul_right [IsOrderedCommMonoid α] : ∀ a b : α, a ≤ b → ∀ c, a * c ≤ b * c := by
  intro a b a_le_b c
  rw [mul_comm _ c, mul_comm _ c]
  apply mul_le_mul_left
  assumption

def mul_le_mul [IsOrderedCommMonoid α] : ∀a b c d: α, a ≤ c -> b ≤ d -> a * b ≤ c * d := by
  intro a b c d ac bd
  apply le_trans
  apply mul_le_mul_left
  assumption
  apply mul_le_mul_right
  assumption
