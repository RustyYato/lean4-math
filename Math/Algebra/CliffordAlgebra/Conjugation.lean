import Math.Algebra.CliffordAlgebra.Defs

namespace CliffordAlgebra

section

variable [RingOps R] [IsRing R] [IsCommMagma R] [AddGroupOps V]
  [IsAddGroup V] [IsAddCommMagma V] [SMul R V] [IsModule R V]

variable {Q: QuadraticForm R V}

def involute : CliffordAlgebra Q →ₐ[R] CliffordAlgebra Q :=
  lift Q {
    val := -CliffordAlgebra.ι Q
    property v := by
      rw [LinearMap.apply_neg, ←neg_mul_left, ←neg_mul_right, neg_neg]
      rw [ι_sq_scalar]
  }

def involute_ι (v: V) : involute (ι Q v) = -ι Q v := by
  rw [involute, lift_ι_apply]
  rfl

def involute_involute (x: CliffordAlgebra Q) : involute (involute x) = x := by
  induction x with
  | algebraMap x => rw [map_algebraMap, map_algebraMap]
  | add a b iha ihb => rw [map_add, map_add, iha, ihb]
  | mul a b iha ihb => rw [map_mul, map_mul, iha, ihb]
  | ι x => rw [involute_ι, map_neg, involute_ι, neg_neg]

def involute_comp_involute : involute.comp (involute (Q := Q)) = AlgHom.id := by
  ext x; show involute (involute x) = x
  rw [involute_involute]

end

end CliffordAlgebra
