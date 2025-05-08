import Math.Algebra.DirectSum.Ring
import Math.Algebra.GradedMonoid.Internal
import Math.Algebra.AddGroupWithOne.SetLike.Basic

namespace SetLike

variable {S: Type*} [SetLike S R] (A: γ -> S)

instance [Add γ]
  [AddMonoidOps R] [Mul R]
  [IsNonUnitalNonAssocSemiring R]
  [IsAddSubmonoid S] [GradedMul A]
  : IsGNonUnitalNonAssocSemiring (fun i => A i) where
  mul_zero {i j} a := by
    apply Subtype.val_inj
    apply mul_zero
  zero_mul {i j} a := by
    apply Subtype.val_inj
    apply zero_mul
  mul_add {i j} a b c := by
    apply Subtype.val_inj
    apply mul_add
  add_mul {i j} a b c := by
    apply Subtype.val_inj
    apply add_mul

instance instSemiringOps [AddMonoidOps γ] [IsAddMonoid γ] [SemiringOps R] [IsSemiring R] [IsAddSubmonoid S] [GradedOne A] [GradedMul A] : GSemiringOps (fun i => A i) where
  natCast n := {
    val := n
    property := by
      induction n with
      | zero =>
        rw [natCast_zero]
        apply mem_zero
      | succ n =>
        rw [natCast_succ]
        apply mem_add
        assumption
        apply GradedOne.mem_one
  }

instance [AddMonoidOps γ] [IsAddMonoid γ]
  [SemiringOps R] [IsSemiring R]
  [IsAddSubmonoid S] [GradedOne A] [GradedMul A]
  : IsGSemiring (fun i => A i) where
  natCast_zero := by
    apply Subtype.val_inj
    apply natCast_zero
  natCast_succ n := by
    apply Subtype.val_inj
    apply natCast_succ

instance [AddMonoidOps γ] [IsAddMonoid γ] [RingOps R] [IsRing R] [IsAddSubgroup S] [GradedOne A] [GradedMul A] : GRingOps (fun i => A i) where
  intCast n := {
    val := n
    property := by
      induction n with
      | ofNat =>
        rw [intCast_ofNat]
        apply ((instSemiringOps A).natCast _).property
      | negSucc n =>
        rw [intCast_negSucc]; apply mem_neg
        apply ((instSemiringOps A).natCast _).property
  }

instance [AddMonoidOps γ] [IsAddMonoid γ] [RingOps R] [IsRing R] [IsAddSubgroup S] [GradedOne A] [GradedMul A] : IsGRing (fun i => A i) where
  intCast_ofNat n := by
    apply Subtype.val_inj
    apply intCast_ofNat
  intCast_negSucc n := by
    apply Subtype.val_inj
    apply intCast_negSucc

end SetLike
