import Math.Algebra.Ring
import Math.Order.Partial

variable (α: Type*) [LT α] [LE α] [Add α] [Zero α] [SMul ℕ α] [Mul α] [One α] [Pow α ℕ]
variable {α₀: Type*} [LT α₀] [LE α₀] [Add α₀] [Zero α₀] [SMul ℕ α₀] [Mul α₀] [One α₀] [Pow α₀ ℕ]

class IsOrderedAddCommMonoid extends IsAddCommMagma α, IsAddMonoid α, IsPartialOrder α : Prop where
  add_le_add_left : ∀ a b : α, a ≤ b → ∀ c, c + a ≤ c + b

class IsOrderedCommMonoid extends IsCommMagma α, IsMonoid α, IsPartialOrder α : Prop where
  mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c, c * a ≤ c * b

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
