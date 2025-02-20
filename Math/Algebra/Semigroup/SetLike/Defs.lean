import Math.Data.Set.Like
import Math.Algebra.AddMul

variable (S: Type*) {α: Type*} [SetLike S α]

class IsMulMem [Mul α] : Prop where
  mem_mul (s: S) {a b: α} : a ∈ s -> b ∈ s -> a * b ∈ s

def mem_mul {S α: Type*} [SetLike S α] [Mul α] [IsMulMem S]
  (s: S) {a b: α} : a ∈ s -> b ∈ s -> a * b ∈ s := IsMulMem.mem_mul s

class IsAddMem [Add α] : Prop where
  mem_add (s: S) {a b: α} : a ∈ s -> b ∈ s -> a + b ∈ s

def mem_add {S α: Type*} [SetLike S α] [Add α] [IsAddMem S]
  (s: S) {a b: α} : a ∈ s -> b ∈ s -> a + b ∈ s := IsAddMem.mem_add s

structure SubSemigroup (α: Type*) [Mul α] where
  carrier: Set α
  mem_mul' {a b: α} : a ∈ carrier -> b ∈ carrier -> a * b ∈ carrier

instance [Mul α] : SetLike (SubSemigroup α) α where
  coe := SubSemigroup.carrier
  coe_inj := by
    intro a b eq; cases a; congr

instance [Mul α] : IsMulMem (SubSemigroup α) where
  mem_mul := SubSemigroup.mem_mul'

structure SubAddSemigroup (α: Type*) [Add α] where
  carrier: Set α
  mem_add' {a b: α} : a ∈ carrier -> b ∈ carrier -> a + b ∈ carrier

instance [Add α] : SetLike (SubAddSemigroup α) α where
  coe := SubAddSemigroup.carrier
  coe_inj := by
    intro a b eq; cases a; congr

instance [Add α] : IsAddMem (SubAddSemigroup α) where
  mem_add := SubAddSemigroup.mem_add'

instance [h: SetLike S α] : SetLike (AddOfMul S) (AddOfMul α) where
  coe a := (a.get: Set α)
  coe_inj := h.coe_inj
instance [h: SetLike S α] : SetLike (MulOfAdd S) (MulOfAdd α) where
  coe a := (a.get: Set α)
  coe_inj := h.coe_inj

instance [SetLike S α] [Add α] [IsAddMem S] : IsMulMem (MulOfAdd S) where
  mem_mul := mem_add (S := S)
instance [SetLike S α] [Mul α] [IsMulMem S] : IsAddMem (AddOfMul S) where
  mem_add := mem_mul (S := S)
