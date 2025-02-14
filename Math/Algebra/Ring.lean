import Math.Type.Notation
import Math.Data.StdInt.Basic
import Math.AxiomBlame
import Math.Ops.Checked
import Math.Algebra.Notation
import Math.Algebra.AddMul
import Math.Relation.Basic

import Math.Algebra.Monoid.Char
import Math.Algebra.Field.Defs

class IsMulAction (R M: Type*) [MonoidOps R] [SMul R M] [IsMonoid R] : Prop where
  one_smul: ∀a: M, (1: R) • a = a
  mul_smul: ∀x y: R, ∀b: M, (x * y) • b = x • y • b

export IsMulAction (one_smul mul_smul)

class IsDistribMulAction (R M: Type*) [MonoidOps R] [AddMonoidOps M] [SMul R M] [IsMonoid R] [IsAddMonoid M] extends IsMulAction R M : Prop where
  smul_zero: ∀a: R, a • (0: M) = 0
  smul_add: ∀a: R, ∀x y: M, a • (x + y) = a • x + a • y

export IsDistribMulAction (smul_zero smul_add)

class IsModule (R M: Type*) [SemiringOps R] [AddMonoidOps M] [SMul R M] [IsSemiring R] [IsAddCommMagma M] [IsAddMonoid M] extends IsDistribMulAction R M: Prop where
  add_smul: ∀r s: R, ∀x: M, (r + s) • x = r • x + s • x
  zero_smul: ∀x: M, (0: R) • x = 0

export IsModule (add_smul zero_smul)

class IsSMulComm (R S A: Type*) [SMul R A] [SMul S A]: Prop where
  smul_comm: ∀(r: R) (s: S) (x: A), r • s • x = s • r • x

export IsSMulComm (smul_comm)

def smul_neg [SMul R M] [RingOps R] [AddGroupOps M] [IsRing R] [IsAddGroup M] [IsDistribMulAction R M]
  (r: R) (x: M) : r • -x = -(r • x) := by
  refine neg_eq_of_add_right ?_
  rw [←smul_add, neg_add_cancel, smul_zero]

def neg_smul [SMul R M] [RingOps R] [AddGroupOps M] [IsRing R] [IsAddGroup M] [IsAddCommMagma M] [IsModule R M]
  (r: R) (x: M) : (-r) • x = -(r • x) := by
  refine neg_eq_of_add_right ?_
  rw [←add_smul, neg_add_cancel, zero_smul]
