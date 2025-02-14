import Math.Algebra.MonoidWithOne.Defs
import Math.Algebra.Group.Defs

def intCastRec [NatCast α] [Neg α] : ℤ -> α
| .ofNat n => NatCast.natCast n
| .negSucc n => -NatCast.natCast n.succ

class AddGroupWithOneOps (α: Type*) extends AddGroupOps α, AddMonoidWithOneOps α, IntCast α where

instance [AddMonoidWithOneOps α] [Neg α] [Sub α] [IntCast α] [SMul ℤ α] : AddGroupWithOneOps α where

class IsAddGroupWithOne (α: Type*) [AddGroupWithOneOps α] extends IsAddGroup α, IsAddMonoidWithOne α: Prop where
  intCast_ofNat (n: ℕ) : ((n: Int): α) = (n: α)
  intCast_negSucc (n: ℕ) : (Int.negSucc n) = -(n.succ: α)

variable [AddGroupWithOneOps α] [IsAddGroupWithOne α]

def intCast_ofNat (n: ℕ) : ((n: Int): α) = (n: α) := IsAddGroupWithOne.intCast_ofNat _
def intCast_negSucc (n: ℕ) : (Int.negSucc n) = -(n.succ: α) := IsAddGroupWithOne.intCast_negSucc _

instance [AddGroupWithOneOps α] [IsAddGroupWithOne α] : IsAddGroupWithOne αᵐᵒᵖ where
  natCast_zero := natCast_zero (α := α)
  natCast_succ := natCast_succ (α := α)
  ofNat_eq_natCast := ofNat_eq_natCast (α := α)
  intCast_ofNat := intCast_ofNat (α := α)
  intCast_negSucc := intCast_negSucc (α := α)

def intCast_eq_zsmul_one [AddGroupWithOneOps α] [IsAddGroupWithOne α] (n: Int) : (n: α) = n • 1  := by
  cases n with
  | ofNat n => rw [Int.ofNat_eq_coe, intCast_ofNat, natCast_eq_nsmul_one, zsmul_ofNat]
  | negSucc n => rw [intCast_negSucc, zsmul_negSucc, natCast_eq_nsmul_one]

def intCast_zero [AddGroupWithOneOps α] [IsAddGroupWithOne α] : ((0: Int): α) = 0 := by
  have : 0 = Int.ofNat 0 := rfl
  erw [this, intCast_ofNat, natCast_zero]

def intCast_one [AddGroupWithOneOps α] [IsAddGroupWithOne α] : ((1: Int): α) = 1 := by
  have : 1 = Int.ofNat 1 := rfl
  erw [this, intCast_ofNat, natCast_one]

def intCast_succ [AddGroupWithOneOps α] [IsAddGroupWithOne α] (a: ℤ) : ((a + 1: Int): α) = a + 1 := by
  rw [intCast_eq_zsmul_one, intCast_eq_zsmul_one, add_zsmul, one_zsmul]

def intCast_pred [AddGroupWithOneOps α] [IsAddGroupWithOne α] (a: ℤ) : ((a - 1: Int): α) = a - 1 := by
  rw [intCast_eq_zsmul_one, intCast_eq_zsmul_one, sub_zsmul, one_zsmul]

def intCast_add [AddGroupWithOneOps α] [IsAddGroupWithOne α] (a b: ℤ) : ((a + b: Int): α) = a + b := by
  simp only [intCast_eq_zsmul_one, add_zsmul]

def intCast_neg [AddGroupWithOneOps α] [IsAddGroupWithOne α] (a: ℤ) : ((-a: Int): α) = -a := by
  symm
  apply neg_eq_of_add_left
  rw [←intCast_add, Int.add_right_neg, intCast_zero]

def intCast_sub [AddGroupWithOneOps α] [IsAddGroupWithOne α] (a b: ℤ) : ((a - b: Int): α) = a - b := by
  rw [Int.sub_eq_add_neg, intCast_add, intCast_neg, sub_eq_add_neg]
