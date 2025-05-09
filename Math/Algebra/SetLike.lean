import Math.Algebra.Notation
import Math.Ops.Checked
import Math.Algebra.AddMul
import Math.Data.Set.Like

section

variable (S R: Type*) {α: Type*} [SetLike S α]

class IsZeroMem [Zero α] where
  protected mem_zero (s: S): 0 ∈ s := by intro s; exact s.mem_zero

class IsOneMem [One α] where
  protected mem_one (s: S): 1 ∈ s := by intro s; exact s.mem_one

class IsAddMem [Add α] where
  protected mem_add (s: S) {a b: α}: a ∈ s -> b ∈ s -> a + b ∈ s := by intro s; exact s.mem_add

class IsMulMem [Mul α] where
  protected mem_mul (s: S) {a b: α}: a ∈ s -> b ∈ s -> a * b ∈ s := by intro s; exact s.mem_mul

class IsNegMem [Neg α] where
  protected mem_neg (s: S) {a: α}: a ∈ s -> -a ∈ s := by intro s; exact s.mem_neg

class IsInvMem [Inv α] where
  protected mem_inv (s: S) {a: α}: a ∈ s -> a⁻¹ ∈ s := by intro s; exact s.mem_inv

class IsInv?Mem [Zero α] [CheckedInv? α] : Prop where
  protected mem_inv? (s: S) {a: α} (nz: a ≠ 0) (h: a ∈ s) : a⁻¹? ∈ s := by intro s; exact s.mem_inv?

class IsSMulMem [SMul R α] where
  protected mem_smul (s: S) (r: R) {a: α}: a ∈ s -> r • a ∈ s := by intro s; exact s.mem_smul

end

section

variable {S R α: Type*} [SetLike S α]


variable [Zero α] [One α] [Add α] [Mul α]
   [Neg α] [Inv α] [CheckedInv? α] [SMul R α]

def mem_zero [IsZeroMem S] (s: S): 0 ∈ s := IsZeroMem.mem_zero _
def mem_one [IsOneMem S] (s: S): 1 ∈ s := IsOneMem.mem_one _
def mem_add [IsAddMem S] (s: S) {a b: α}: a ∈ s -> b ∈ s -> a + b ∈ s := IsAddMem.mem_add _
def mem_mul [IsMulMem S] (s: S) {a b: α}: a ∈ s -> b ∈ s -> a * b ∈ s := IsMulMem.mem_mul _
def mem_neg [IsNegMem S] (s: S) {a: α}: a ∈ s -> -a ∈ s := IsNegMem.mem_neg _
def mem_inv [IsInvMem S] (s: S) {a: α}: a ∈ s -> a⁻¹ ∈ s := IsInvMem.mem_inv _
def mem_inv? [IsInv?Mem S] (s: S) {a: α} (nz: a ≠ 0) (h: a ∈ s) : a⁻¹? ∈ s := IsInv?Mem.mem_inv? s nz h
def mem_smul [IsSMulMem S R] (s: S) (r: R) {a: α}: a ∈ s -> r • a ∈ s := IsSMulMem.mem_smul _ _

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

instance [SetLike S α] [Zero α] [IsZeroMem S] : IsOneMem (MulOfAdd S) where
  mem_one := mem_zero (S := S)
instance [SetLike S α] [One α] [IsOneMem S] : IsZeroMem (AddOfMul S) where
  mem_zero := mem_one (S := S)

end

section

variable (R α: Type*)

structure SubZero [Zero α] where
  carrier: Set α
  protected mem_zero: 0 ∈ carrier

structure SubOne [One α] where
  carrier: Set α
  protected mem_one: 1 ∈ carrier

structure AddSubsemigroup [Add α] where
  carrier: Set α
  protected mem_add {a b: α}: a ∈ carrier -> b ∈ carrier -> a + b ∈ carrier

structure Subsemigroup [Mul α] where
  carrier: Set α
  protected mem_mul {a b: α}: a ∈ carrier -> b ∈ carrier -> a * b ∈ carrier

structure SubNeg [Neg α] where
  carrier: Set α
  protected mem_neg {a: α}: a ∈ carrier -> -a ∈ carrier

structure SubInv [Inv α] where
  carrier: Set α
  protected mem_inv {a: α}: a ∈ carrier -> a⁻¹ ∈ carrier

structure SubInv? [Zero α] [CheckedInv? α] where
  carrier: Set α
  protected mem_inv? {a: α} (nz: a ≠ 0) (h: a ∈ carrier) : a⁻¹? ∈ carrier

structure SubMulAction [SMul R α] where
  carrier: Set α
  protected mem_smul (r: R) {a: α}: a ∈ carrier -> r • a ∈ carrier

end

section

variable {R α: Type*}

namespace SubZero

variable [Zero α]

instance : SetLike (SubZero α) α where
instance : IsZeroMem (SubZero α) where

def copy (s: SubZero α) (U: Set α) (h: s = U) : SubZero α where
  carrier := U
  mem_zero := h ▸ s.mem_zero

end SubZero

namespace SubOne

variable [One α]

instance : SetLike (SubOne α) α where
instance : IsOneMem (SubOne α) where

def copy (s: SubOne α) (U: Set α) (h: s = U) : SubOne α where
  carrier := U
  mem_one := h ▸ s.mem_one

end SubOne

namespace AddSubsemigroup

variable [Add α]

instance : SetLike (AddSubsemigroup α) α where
instance : IsAddMem (AddSubsemigroup α) where

def copy (s: AddSubsemigroup α) (U: Set α) (h: s = U) : AddSubsemigroup α where
  carrier := U
  mem_add := h ▸ s.mem_add

end AddSubsemigroup

namespace Subsemigroup

variable [Mul α]

instance : SetLike (Subsemigroup α) α where
instance : IsMulMem (Subsemigroup α) where

def copy (s: Subsemigroup α) (U: Set α) (h: s = U) : Subsemigroup α where
  carrier := U
  mem_mul := h ▸ s.mem_mul

end Subsemigroup

namespace SubNeg

variable [Neg α]

instance : SetLike (SubNeg α) α where
instance : IsNegMem (SubNeg α) where

def copy (s: SubNeg α) (U: Set α) (h: s = U) : SubNeg α where
  carrier := U
  mem_neg := h ▸ s.mem_neg

end SubNeg

namespace SubInv

variable [Inv α]

instance : SetLike (SubInv α) α where
instance : IsInvMem (SubInv α) where

def copy (s: SubInv α) (U: Set α) (h: s = U) : SubInv α where
  carrier := U
  mem_inv := h ▸ s.mem_inv

end SubInv

namespace SubInv?

variable [Zero α] [CheckedInv? α]

instance : SetLike (SubInv? α) α where
instance : IsInv?Mem (SubInv? α) where

def copy (s: SubInv? α) (U: Set α) (h: s = U) : SubInv? α where
  carrier := U
  mem_inv? := h ▸ s.mem_inv?

end SubInv?

namespace SubMulAction

variable [SMul R α]

instance : SetLike (SubMulAction R α) α where
instance : IsSMulMem (SubMulAction R α) R where

def copy (s: SubMulAction R α) (U: Set α) (h: s = U) : SubMulAction R α where
  carrier := U
  mem_smul := h ▸ s.mem_smul

end SubMulAction

end
