import Math.Algebra.Monoid.Defs
import Math.Data.Nat.Cast

def natCastRec [Add α] [Zero α] [One α] : ℕ -> α
| 0 => 0
| n + 1 => natCastRec n + 1

def instNatCast [Add α] [Zero α] [One α] : NatCast α := ⟨natCastRec⟩

class AddMonoidWithOneOps (α: Type*) extends AddMonoidOps α, One α, NatCast α where

instance (priority := 50) instAddMonoidOpsWithOne [AddMonoidOps α] [One α] [NatCast α] : AddMonoidWithOneOps α where

class IsAddMonoidWithOne (α: Type*) [AddMonoidWithOneOps α] : Prop extends IsAddMonoid α where
  natCast_zero : ((0: Nat): α) = (0: α)
  natCast_succ (n: ℕ) : (n.succ: α) = (n: α) + (1: α)

variable [AddMonoidWithOneOps α] [IsAddMonoidWithOne α]

@[norm_cast, simp]
def natCast_zero : ((0: Nat): α) = (0: α) := IsAddMonoidWithOne.natCast_zero
@[norm_cast]
def natCast_succ (n: ℕ) : (n.succ: α) = (n: α) + (1: α) := IsAddMonoidWithOne.natCast_succ _

def natCast_eq_nsmul_one (n: Nat) : (n: α) = n • 1  := by
  induction n with
  | zero => rw [zero_nsmul, natCast_zero]
  | succ n ih => rw [natCast_succ, ih, succ_nsmul]

@[norm_cast, simp]
def natCast_one : ((1: Nat): α) = 1 := by
  rw [natCast_succ, natCast_zero, zero_add]

@[norm_cast]
def natCast_add (a b: ℕ) : ((a + b: Nat): α) = a + b := by
  simp [natCast_eq_nsmul_one, add_nsmul]

instance : AddMonoidWithOneOps αᵃᵒᵖ := instAddMonoidOpsWithOne

instance : IsAddMonoidWithOne αᵃᵒᵖ where
  natCast_zero := natCast_zero (α := α)
  natCast_succ n := by
    show (n.succ: α) = 1 + (n: α)
    rw [←natCast_one, ←natCast_add, Nat.add_comm]

instance : IsAddMonoidWithOne αᵐᵒᵖ where
  natCast_zero := natCast_zero (α := α)
  natCast_succ := natCast_succ (α := α)
