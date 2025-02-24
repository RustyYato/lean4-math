import Math.Algebra.Ring.Defs
import Math.Algebra.Monoid.Action.Defs

class IsModule (R M: Type*) [SMul R M] [SemiringOps R] [AddMonoidOps M] [IsSemiring R]
  [IsAddCommMagma M] [IsAddMonoid M] extends IsDistribMulAction R M: Prop where
  add_smul: ∀r s: R, ∀x: M, (r + s) • x = r • x + s • x
  zero_smul: ∀x: M, (0: R) • x = 0

def add_smul [SemiringOps R] [AddMonoidOps M] [SMul R M] [IsAddCommMagma M] [IsAddMonoid M] [IsSemiring R] [IsModule R M]: ∀r s: R, ∀x: M, (r + s) • x = r • x + s • x := IsModule.add_smul
def zero_smul [SemiringOps R] [AddMonoidOps M] [SMul R M] [IsAddCommMagma M] [IsAddMonoid M] [IsSemiring R] [IsModule R M]: ∀x: M, (0: R) • x = 0 := IsModule.zero_smul

def neg_smul [SMul R M] [RingOps R] [AddGroupOps M] [IsRing R] [IsAddGroup M] [IsAddCommMagma M] [IsModule R M]
  (r: R) (x: M) : (-r) • x = -(r • x) := by
  refine neg_eq_of_add_right ?_
  rw [←add_smul, neg_add_cancel, zero_smul]

instance instDistribMulActionSelf [AddMonoidOps R] [IsAddMonoid R] [MonoidOps R] [IsMonoid R] [IsLeftDistrib R] [IsMulZeroClass R] : IsDistribMulAction R R where
  smul_zero _ := mul_zero _
  smul_add _ _ _ := mul_add _ _ _

instance instModuleSelf [SemiringOps R] [IsSemiring R] : IsModule R R where
  add_smul _ _ _ := add_mul _ _ _
  zero_smul _ := zero_mul _

instance [AddMonoidWithOneOps R] [IsAddMonoidWithOne R] [IsAddCommMagma R] : IsModule Nat R where
  one_smul := one_nsmul
  mul_smul _ _ _ := mul_nsmul _ _ _
  smul_zero := nsmul_zero
  smul_add := nsmul_add
  add_smul := add_nsmul
  zero_smul := zero_nsmul
