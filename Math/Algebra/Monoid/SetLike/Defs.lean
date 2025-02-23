import Math.Algebra.Semigroup.SetLike.Defs
import Math.Algebra.Notation

variable (S: Type*) {α: Type*} [SetLike S α]

class IsOneMem [One α] : Prop where
  mem_one (s: S) : 1 ∈ s

def mem_one {S α: Type*} [SetLike S α] [One α] [IsOneMem S]
  (s: S) : 1 ∈ s := IsOneMem.mem_one s

class IsZeroMem [Zero α] : Prop where
  mem_zero (s: S) : 0 ∈ s

def mem_zero {S α: Type*} [SetLike S α] [Zero α] [IsZeroMem S]
  (s: S) : 0 ∈ s := IsZeroMem.mem_zero s

class IsSubmonoid [Mul α] [One α] extends IsMulMem S, IsOneMem S: Prop where
class IsAddSubmonoid [Add α] [Zero α] extends IsAddMem S, IsZeroMem S: Prop where

structure Submonoid (α: Type*) [Mul α] [One α] extends SubSemigroup α where
  mem_one': 1 ∈ carrier

instance [Mul α] [One α] : SetLike (Submonoid α) α where
  coe a := a.carrier
  coe_inj := by
    intro a b eq; cases a; congr
    apply SetLike.coe_inj
    assumption

instance [Mul α] [One α] : IsSubmonoid (Submonoid α) where
  mem_mul a := a.mem_mul'
  mem_one a := a.mem_one'

@[ext]
def Submonoid.ext [Mul α] [One α] (a b: Submonoid α) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _

structure AddSubmonoid (α: Type*) [Add α] [Zero α] extends AddSubSemigroup α where
  mem_zero': 0 ∈ carrier

instance [Add α] [Zero α] : SetLike (AddSubmonoid α) α where
  coe a := a.carrier
  coe_inj := by
    intro a b eq; cases a; congr
    apply SetLike.coe_inj
    assumption

instance [Add α] [Zero α] : IsAddSubmonoid (AddSubmonoid α) where
  mem_add a := a.mem_add'
  mem_zero a := a.mem_zero'

@[ext]
def AddSubmonoid.ext [Add α] [Zero α] (a b: AddSubmonoid α) : (∀x, x ∈ a ↔ x ∈ b) -> a = b := SetLike.ext _ _

instance [SetLike S α] [Add α] [Zero α] [IsAddSubmonoid S] : IsSubmonoid (MulOfAdd S) where
  mem_one := mem_zero (S := S)
instance [SetLike S α] [Mul α] [One α] [IsSubmonoid S] : IsAddSubmonoid (AddOfMul S) where
  mem_zero := mem_one (S := S)
