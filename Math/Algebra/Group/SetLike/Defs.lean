import Math.Algebra.Monoid.SetLike.Defs
import Math.Algebra.Notation

variable (S: Type*) {α: Type*} [SetLike S α]

class IsInvMem [Inv α] : Prop where
  mem_inv (s: S) {a: α} (h: a ∈ s) : a⁻¹ ∈ s

def mem_inv {S α: Type*} [SetLike S α] [Inv α] [IsInvMem S] (s: S) {a: α} (h: a ∈ s) : a⁻¹ ∈ s := IsInvMem.mem_inv s h

class IsNegMem [Neg α] : Prop where
  mem_neg (s: S) {a: α} (h: a ∈ s) : -a ∈ s

def mem_neg {S α: Type*} [SetLike S α] [Neg α] [IsNegMem S] (s: S) {a: α} (h: a ∈ s) : -a ∈ s := IsNegMem.mem_neg s h

class IsSubGroup [Mul α] [One α] [Inv α] extends IsSubMonoid S, IsInvMem S: Prop where
class IsSubAddGroup [Add α] [Zero α] [Neg α] extends IsSubAddMonoid S, IsNegMem S: Prop where

structure SubGroup (α: Type*) [Mul α] [One α] [Inv α] extends SubMonoid α where
  mem_inv': ∀{a}, a ∈ carrier -> a⁻¹ ∈ carrier

instance [Mul α] [One α] [Inv α] : SetLike (SubGroup α) α where
  coe a := a.carrier
  coe_inj := by
    intro a b eq; cases a; congr
    apply SetLike.coe_inj
    assumption

instance [Mul α] [One α] [Inv α] : IsSubGroup (SubGroup α) where
  mem_mul a := a.mem_mul'
  mem_one a := a.mem_one'
  mem_inv a := a.mem_inv'

structure SubAddGroup (α: Type*) [Add α] [Zero α] [Neg α] extends SubAddMonoid α where
  mem_neg': ∀{a}, a ∈ carrier -> -a ∈ carrier

instance [Add α] [Zero α] [Neg α] : SetLike (SubAddGroup α) α where
  coe a := a.carrier
  coe_inj := by
    intro a b eq; cases a; congr
    apply SetLike.coe_inj
    assumption

instance [Add α] [Zero α] [Neg α] : IsSubAddGroup (SubAddGroup α) where
  mem_add a := a.mem_add'
  mem_zero a := a.mem_zero'
  mem_neg a := a.mem_neg'

instance [SetLike S α] [Add α] [Zero α] [Neg α] [IsSubAddGroup S] : IsSubGroup (MulOfAdd S) where
  mem_inv := mem_neg (S := S)
instance [SetLike S α] [Mul α] [One α] [Inv α] [IsSubGroup S] : IsSubAddGroup (AddOfMul S) where
  mem_neg := mem_inv (S := S)
