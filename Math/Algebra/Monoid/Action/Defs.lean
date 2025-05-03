import Math.Algebra.Notation
import Math.Algebra.Group.Defs

class IsMulAction (R M: Type*) [SMul R M] [MonoidOps R] [IsMonoid R]: Prop where
  one_smul: ∀a: M, (1: R) • a = a
  mul_smul: ∀x y: R, ∀b: M, (x * y) • b = x • y • b

@[simp] def one_smul [MonoidOps R] [SMul R M] [IsMonoid R] [IsMulAction R M]: ∀a: M, (1: R) • a = a := IsMulAction.one_smul
def mul_smul [MonoidOps R] [SMul R M] [IsMonoid R] [IsMulAction R M]: ∀x y: R, ∀b: M, (x * y) • b = x • y • b := IsMulAction.mul_smul

class IsSMulZeroClass (R M: Type*) [Zero M] [SMul R M] : Prop where
  smul_zero: ∀a: R, a • (0: M) = 0

@[simp] def smul_zero [Zero M] [SMul R M] [IsSMulZeroClass R M]: ∀a: R, a • (0: M) = 0 := IsSMulZeroClass.smul_zero

class IsDistribMulAction (R M: Type*) [SMul R M] [MonoidOps R] [AddMonoidOps M] [IsMonoid R] [IsAddMonoid M] : Prop extends IsMulAction R M, IsSMulZeroClass R M where
  smul_add: ∀a: R, ∀x y: M, a • (x + y) = a • x + a • y

def smul_add [MonoidOps R] [AddMonoidOps M] [SMul R M] [IsMonoid R] [IsAddMonoid M] [IsDistribMulAction R M]: ∀a: R, ∀x y: M, a • (x + y) = a • x + a • y := IsDistribMulAction.smul_add

class IsZeroSMulClass (R M: Type*) [Zero R] [Zero M] [SMul R M] : Prop where
 zero_smul (m: M): (0: R) • m = 0

@[simp] def zero_smul [Zero R] [Zero M] [SMul R M] [IsZeroSMulClass R M]: ∀x: M, (0: R) • x = 0 := IsZeroSMulClass.zero_smul

class IsSMulComm (R S A: Type*) [SMul R A] [SMul S A]: Prop where
  smul_comm: ∀(r: R) (s: S) (x: A), r • s • x = s • r • x

def smul_comm [SMul R A] [SMul S A] [IsSMulComm R S A]: ∀(r: R) (s: S) (x: A), r • s • x = s • r • x := IsSMulComm.smul_comm

instance (priority := 500) [SMul R A] [SMul S A] [IsSMulComm R S A] : IsSMulComm S R A where
  smul_comm _ _ _ := (smul_comm _ _ _).symm

class IsScalarTower (R S A : Type*) [SMul R S] [SMul S A] [SMul R A] : Prop where
  smul_assoc : ∀ (x : R) (y : S) (z : A), (x • y) • z = x • y • z

def smul_assoc [SMul R S] [SMul S A] [SMul R A] [IsScalarTower R S A] : ∀ (x : R) (y : S) (z : A), (x • y) • z = x • y • z := IsScalarTower.smul_assoc

@[simp]
def smul_eq_mul [Mul α] (a b: α) : a • b = a * b := rfl

class IsCentralScalar (M α : Type*) [SMul M α] [SMul Mᵐᵒᵖ α]: Prop where
  op_smul_eq_smul : ∀(m : M) (a : α), MulOpp.mk m • a = m • a

def op_smul_eq_smul [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] : ∀(m : M) (a : α), MulOpp.mk m • a = m • a := IsCentralScalar.op_smul_eq_smul

instance [Mul α] [IsCommMagma α] [IsSemigroup α] : IsSMulComm α α α where
  smul_comm  r s x := by
    simp [SMul.smul]
    rw [mul_left_comm]

instance [MonoidOps M] [IsMonoid M] [IsCommMagma M] [SMul M α] [IsMulAction M α] : IsSMulComm M M α where
  smul_comm  r s x := by
    rw [←mul_smul, mul_comm,mul_smul]

instance [SMul Mᵐᵒᵖ α] [SMul M α] [IsCentralScalar M α] [IsSMulComm M M α] : IsSMulComm Mᵐᵒᵖ M α where
  smul_comm r m x := by
    have : r = MulOpp.mk r.get := rfl
    rw [this]
    rw [op_smul_eq_smul, op_smul_eq_smul, smul_comm]

instance [SMul Mᵐᵒᵖ α] [SMul M α] [IsCentralScalar M α] [IsSMulComm M M α] : IsSMulComm M Mᵐᵒᵖ α where
  smul_comm r m x := by
    have : m = MulOpp.mk m.get := rfl
    rw [this]
    rw [op_smul_eq_smul, op_smul_eq_smul, smul_comm]

instance [MonoidOps R] [IsMonoid R] : IsMulAction R R where
  one_smul _ := one_mul _
  mul_smul _ _ _ := mul_assoc _ _ _

instance [AddMonoidOps A] [IsAddMonoid A]
  [SMul R A] [MonoidOps R] [IsMonoid R]
  [IsDistribMulAction R A]
  : IsSMulComm ℕ R A where
  smul_comm := by
    intro n r a
    induction n with
    | zero => rw [zero_nsmul, zero_nsmul, smul_zero]
    | succ n ih => rw [succ_nsmul, succ_nsmul, smul_add, ih]

-- low priority so we try to find a more direct instance when possible
instance (priority := 100) [SMul R A] [SMul S A] [IsSMulComm R S A]
  : IsSMulComm S R A where
  smul_comm := by
    intro r s a; symm
    apply smul_comm

instance [AddMonoidOps α] [IsAddMonoid α] [IsAddCommMagma α] : IsDistribMulAction ℕ α where
  one_smul _ := one_nsmul _
  mul_smul _ _ _ := mul_nsmul _ _ _
  smul_zero := nsmul_zero
  smul_add := nsmul_add

def neg_smul' [SMul R M] [MonoidOps R] [AddGroupOps M] [IsMonoid R] [IsAddGroup M] [IsAddCommMagma M] [IsDistribMulAction R M]
  (r: R) (x: M) : r • (-x) = -(r • x) := by
  refine neg_eq_of_add_right ?_
  rw [←smul_add, neg_add_cancel, smul_zero]

instance [MonoidOps R] [IsMonoid R] [SMul R M] [IsMulAction R M] : IsScalarTower R R M where
  smul_assoc r a b := by rw [smul_eq_mul, mul_smul]

instance [Zero M] [Mul M] [IsMulZeroClass M] : IsSMulZeroClass M M where
  smul_zero := by simp

instance [AddMonoidOps M] [IsAddMonoid M] : IsSMulZeroClass ℕ M where
  smul_zero := by simp

instance [AddGroupOps M] [IsSubNegMonoid M] [IsNegZeroClass M] : IsSMulZeroClass ℤ M where
  smul_zero := by simp

instance [Zero M] [Mul M] [IsMulZeroClass M] : IsZeroSMulClass M M where
  zero_smul := by simp

instance [AddMonoidOps M] [IsAddMonoid M] : IsZeroSMulClass ℕ M where
  zero_smul := by simp

instance [AddGroupOps M] [IsSubNegMonoid M] : IsZeroSMulClass ℤ M where
  zero_smul := by simp
