import Math.Algebra.Monoid.Defs

def natCastRec [Add α] [Zero α] [One α] : ℕ -> α
| 0 => 0
| n + 1 => natCastRec n + 1

def instNatCast [Add α] [Zero α] [One α] : NatCast α := ⟨natCastRec⟩

class AddMonoidWithOneOps (α: Type*) extends AddMonoidOps α, One α, NatCast α where
  ofNat n : OfNat α (n + 2) := by infer_instance

instance [AddMonoidOps α] [One α] [NatCast α] [∀n, OfNat α (n + 2)] : AddMonoidWithOneOps α where

instance (priority := 50) [AddMonoidWithOneOps α] : OfNat α (n + 2) := AddMonoidWithOneOps.ofNat n

class IsAddMonoidWithOne (α: Type*) [AddMonoidWithOneOps α] extends IsAddMonoid α: Prop where
  natCast_zero : ((0: Nat): α) = (0: α)
  natCast_succ (n: ℕ) : (n.succ: α) = (n: α) + (1: α)
  ofNat_eq_natCast (n: ℕ): OfNat.ofNat (α := α) (n + 2) = ((n + 2: Nat): α)

variable [AddMonoidWithOneOps α] [IsAddMonoidWithOne α]

def natCast_zero : ((0: Nat): α) = (0: α) := IsAddMonoidWithOne.natCast_zero
def natCast_succ (n: ℕ) : (n.succ: α) = (n: α) + (1: α) := IsAddMonoidWithOne.natCast_succ _
def ofNat_eq_natCast (n: ℕ): OfNat.ofNat (α := α) (n + 2) = ((n + 2: Nat): α) := IsAddMonoidWithOne.ofNat_eq_natCast _

instance [AddMonoidWithOneOps α] [IsAddMonoidWithOne α] : IsAddMonoidWithOne αᵐᵒᵖ where
  natCast_zero := natCast_zero (α := α)
  natCast_succ := natCast_succ (α := α)
  ofNat_eq_natCast := ofNat_eq_natCast (α := α)

def natCast_eq_nsmul_one [AddMonoidWithOneOps α] [IsAddMonoidWithOne α] (n: Nat) : (n: α) = n • 1  := by
  induction n with
  | zero => rw [zero_nsmul, natCast_zero]
  | succ n ih => rw [natCast_succ, ih, succ_nsmul]

def natCast_one [AddMonoidWithOneOps α] [IsAddMonoidWithOne α] : ((1: Nat): α) = 1 := by
  rw [natCast_succ, natCast_zero, zero_add]

def natCast_add [AddMonoidWithOneOps α] [IsAddMonoidWithOne α] (a b: ℕ) : ((a + b: Nat): α) = a + b := by
  simp [natCast_eq_nsmul_one, add_nsmul]
