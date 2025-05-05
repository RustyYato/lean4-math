-- prove that the CliffordAlgebra is isomorphic the exterior algebra
-- which we represent as CliffordAlgebra (0: QuadraticForm R M)

import Math.Algebra.CliffordAlgebra.Conjugation
import Math.Algebra.Module.LinearMap.End

open scoped LinearMap.End

abbrev ExteriorAlgebra (R V: Type*)
  [SemiringOps R] [IsSemiring R] [IsCommMagma R] [AddMonoidOps V]
  [IsAddMonoid V] [IsAddCommMagma V] [SMul R V] [IsModule R V] :=
  CliffordAlgebra (0: QuadraticForm R V)

namespace ExteriorAlgebra

section

variable (R: Type*) {V: Type*} [SemiringOps R] [IsSemiring R] [IsCommMagma R] [AddMonoidOps V]
  [IsAddMonoid V] [IsAddCommMagma V] [SMul R V] [IsModule R V]


def ι : V -> ExteriorAlgebra R V := CliffordAlgebra.ι 0
@[simp] def ι_sq_zero (v: V): ι R v * ι R v = 0 := by
  erw [CliffordAlgebra.ι_sq_scalar 0 v, map_zero]

def lift [SMul R A] [SemiringOps A] [AlgebraMap R A] [IsSemiring A] [IsAlgebra R A] :
    { f : V →ₗ[R] A // ∀ m, f m * f m = 0 } ≃ (ExteriorAlgebra R V →ₐ[R] A) :=
    flip Equiv.trans (CliffordAlgebra.lift 0) <| {
      toFun f := ⟨f.val, fun m => (map_zero (algebraMap (R := R) (α := A))).symm ▸ f.property m⟩
      invFun f := ⟨f.val, fun m => (map_zero (algebraMap (R := R) (α := A))).symm ▸ f.property m⟩
      leftInv _ := rfl
      rightInv _ := rfl
    }

def apply_lift_ι [SMul R A] [SemiringOps A] [AlgebraMap R A] [IsSemiring A] [IsAlgebra R A] (f: { f : V →ₗ[R] A // ∀ m, f m * f m = 0 }) (v: V) :
  lift R f (ι R v) = f.val v := CliffordAlgebra.lift_ι_apply _ _ _

@[elab_as_elim, induction_eliminator]
def induction {C : ExteriorAlgebra R V → Prop}
  (algebraMap: ∀r: R, C (algebraMap r)) (ι: ∀ x, C (ι R x))
  (mul: ∀ a b, C a → C b → C (a * b)) (add: ∀ a b, C a → C b → C (a + b))
  (a : ExteriorAlgebra R V) : C a :=
  CliffordAlgebra.induction (Q := 0) algebraMap ι mul add a

end

end ExteriorAlgebra

namespace CliffordAlgebra

variable [RingOps R] [IsRing R] [IsCommMagma R] [AddGroupOps V]
  [IsAddGroup V] [IsAddCommMagma V] [SMul R V] [IsModule R V] [IsInvertible (2: R)]

variable {Q: QuadraticForm R V}

-- set_option trace.Meta.synthInstance true in
-- set_option trace.Meta.synthInstance.resume false in

def pre_vector_wedge (v: V) : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q where
  toFun x := ⅟(2: R) • (ι Q v * x + involute Q x * ι Q v)
  map_add {x y} := by
    rw [map_add (involute Q)]
    rw [←smul_add]
    congr 1
    simp only [mul_add, add_mul]
    repeat rw [←add_assoc]
    rw [add_comm_right _ ((ι Q v) * y)]
  map_smul := by
    intro r x
    rw [map_smul, smul_def r, ←mul_assoc, ←commutes, mul_assoc,
      smul_def r, mul_assoc, ←smul_def, ←smul_def, ←smul_add,
      smul_comm]

def apply_pre_vector_wedge (v: V) (x: CliffordAlgebra Q) : pre_vector_wedge v x = ⅟(2: R) • (ι Q v * x + involute Q x * ι Q v) := rfl

def pre_vector_wedge_sq_zero (v: V) (x: CliffordAlgebra Q) : pre_vector_wedge v (pre_vector_wedge v x) = 0 := by
  rw [apply_pre_vector_wedge, apply_pre_vector_wedge]
  simp [smul_def]
  rw [←mul_assoc, ←commutes, mul_assoc, map_mul, mul_assoc,
  map_algebraMap, ←mul_add, map_add, map_mul, involute_ι,
  map_mul, involute_involute, involute_ι, ←mul_assoc,
  neg_mul, mul_neg, add_mul, mul_add (ι Q v),
  neg_mul, neg_mul, mul_assoc x,
  ι_sq_scalar, ←mul_assoc, ι_sq_scalar]
  rw [commutes _ x, add_assoc, ←add_assoc _ (-_), ←mul_assoc,
  add_neg_cancel, zero_add, add_neg_cancel, mul_zero]

def vector_wedge (Q: QuadraticForm R V) : V →ₗ[R] CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q where
  toFun := pre_vector_wedge
  map_add {x y} := by
    ext a
    rw [LinearMap.apply_add]; simp [apply_pre_vector_wedge]
    rw [map_add, add_mul, mul_add, ←smul_add]; congr 1
    ac_rfl
  map_smul := by
    intro r x
    ext a
    rw [LinearMap.apply_smul]; simp [apply_pre_vector_wedge]
    rw [map_smul, smul_comm]; congr 1; simp [smul_def r]
    rw [mul_add, mul_assoc]; congr 1
    rw [←mul_assoc, ←mul_assoc, commutes]

def apply_vector_wedge (Q: QuadraticForm R V) : vector_wedge Q v = pre_vector_wedge v := rfl

def vector_wedge_sq_zero (v: V) (x: CliffordAlgebra Q) : vector_wedge Q v (vector_wedge Q v x) = 0 := by
  apply pre_vector_wedge_sq_zero

def ext_to_cliff_end (Q: QuadraticForm R V) : ExteriorAlgebra R V →ₐ[R] (CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q) :=
  ExteriorAlgebra.lift R {
    val := vector_wedge Q
    property v := by
      ext
      apply vector_wedge_sq_zero
  }

def apply_ext_to_cliff_end_ι (Q: QuadraticForm R V) (v: V) :
  ext_to_cliff_end Q (ExteriorAlgebra.ι R v) = vector_wedge Q v :=
  ExteriorAlgebra.apply_lift_ι _ _ _

-- def ext_to_cliff_end_mul (a b: ExteriorAlgebra R V) :
--   ext_to_cliff_end Q a 1 * ext_to_cliff_end Q b 1 = ext_to_cliff_end Q (a * b) 1 := by
--   rw [map_mul]
--   show _ = ext_to_cliff_end Q a (ext_to_cliff_end Q b 1)
--   generalize ext_to_cliff_end Q b 1 = x
--   induction a generalizing x with
--   | algebraMap r =>
--     rw [map_algebraMap]
--     show (r • (1 : _ →ₗ[R] _)) 1 * _ = _
--     rw [LinearMap.apply_smul, LinearMap.apply_one, smul_def, mul_one]
--     rfl
--   | add a b iha ihb =>
--     rw [map_add,
--       LinearMap.apply_add,
--       LinearMap.apply_add, add_mul,
--       iha, ihb]
--   | mul a b iha ihb =>
--     rw [map_mul,
--       LinearMap.End.apply_mul,
--       LinearMap.End.apply_mul,
--       ←ihb x]
--     sorry
--   | ι => sorry


def ofExteriorₗ : ExteriorAlgebra R V →ₗ[R] CliffordAlgebra Q :=
  (ext_to_cliff_end (Q := Q)).toLinearMap.swap 1

def lineqvExterior : ExteriorAlgebra R V ≃ₗ[R] CliffordAlgebra Q := {
  ofExteriorₗ with
  invFun := sorry
  leftInv := sorry
  rightInv := sorry
}

end CliffordAlgebra
