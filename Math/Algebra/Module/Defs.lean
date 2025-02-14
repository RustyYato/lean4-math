import Math.Algebra.Ring.Defs
import Math.Algebra.Monoid.Action.Defs

class IsModule (R M: Type*) [SemiringOps R] [AddMonoidOps M] [SMul R M] [IsSemiring R]
  [IsAddCommMagma M] [IsAddMonoid M] extends IsDistribMulAction R M: Prop where
  add_smul: ∀r s: R, ∀x: M, (r + s) • x = r • x + s • x
  zero_smul: ∀x: M, (0: R) • x = 0

def add_smul [SemiringOps R] [AddMonoidOps M] [SMul R M] [IsAddCommMagma M] [IsAddMonoid M] [IsSemiring R] [IsModule R M]: ∀r s: R, ∀x: M, (r + s) • x = r • x + s • x := IsModule.add_smul
def zero_smul [SemiringOps R] [AddMonoidOps M] [SMul R M] [IsAddCommMagma M] [IsAddMonoid M] [IsSemiring R] [IsModule R M]: ∀x: M, (0: R) • x = 0 := IsModule.zero_smul

def neg_smul [SMul R M] [RingOps R] [AddGroupOps M] [IsRing R] [IsAddGroup M] [IsAddCommMagma M] [IsModule R M]
  (r: R) (x: M) : (-r) • x = -(r • x) := by
  refine neg_eq_of_add_right ?_
  rw [←add_smul, neg_add_cancel, zero_smul]
