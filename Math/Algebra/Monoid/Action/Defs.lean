import Math.Algebra.Notation
import Math.Algebra.Monoid.Defs

class IsMulAction (R M: Type*) [SMul R M] [MonoidOps R] [IsMonoid R]: Prop where
  one_smul: ∀a: M, (1: R) • a = a
  mul_smul: ∀x y: R, ∀b: M, (x * y) • b = x • y • b

def one_smul [MonoidOps R] [SMul R M] [IsMonoid R] [IsMulAction R M]: ∀a: M, (1: R) • a = a := IsMulAction.one_smul
def mul_smul [MonoidOps R] [SMul R M] [IsMonoid R] [IsMulAction R M]: ∀x y: R, ∀b: M, (x * y) • b = x • y • b := IsMulAction.mul_smul

class IsDistribMulAction (R M: Type*) [SMul R M] [MonoidOps R] [AddMonoidOps M] [IsMonoid R] [IsAddMonoid M] extends IsMulAction R M: Prop where
  smul_zero: ∀a: R, a • (0: M) = 0
  smul_add: ∀a: R, ∀x y: M, a • (x + y) = a • x + a • y

def smul_zero [MonoidOps R] [AddMonoidOps M] [SMul R M] [IsMonoid R] [IsAddMonoid M] [IsDistribMulAction R M]: ∀a: R, a • (0: M) = 0 := IsDistribMulAction.smul_zero
def smul_add [MonoidOps R] [AddMonoidOps M] [SMul R M] [IsMonoid R] [IsAddMonoid M] [IsDistribMulAction R M]: ∀a: R, ∀x y: M, a • (x + y) = a • x + a • y := IsDistribMulAction.smul_add

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
