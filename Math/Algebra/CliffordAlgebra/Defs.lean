import Math.Algebra.TensorAlgebra.Basic
import Math.Algebra.QuadraticForm.Basic

section

variable [SemiringOps R] [IsSemiring R] [IsCommMagma R] [AddMonoidOps V]
  [IsAddMonoid V] [IsAddCommMagma V] [SMul R V] [IsModule R V]

variable (Q: QuadraticForm R V)

open TensorAlgebra in
inductive CliffordAlgebra.Rel : TensorAlgebra R V -> TensorAlgebra R V -> Prop where
| intro (a: V) : Rel (ι R a * ι R a) (algebraMap (Q a))

def CliffordAlgebra := RingQuot (CliffordAlgebra.Rel Q)

end

section Instances

open CliffordAlgebra

variable [SemiringOps R] [IsSemiring R] [IsCommMagma R] [AddMonoidOps V]
  [IsAddMonoid V] [IsAddCommMagma V] [SMul R V] [IsModule R V]

variable (Q: QuadraticForm R V)

instance : SemiringOps (CliffordAlgebra Q) := inferInstanceAs (SemiringOps (RingQuot (Rel Q)))
instance : SMul R (CliffordAlgebra Q) := inferInstanceAs (SMul R (RingQuot (Rel Q)))
instance : AlgebraMap R (CliffordAlgebra Q) := inferInstanceAs (AlgebraMap R (RingQuot (Rel Q)))
instance : IsSemiring (CliffordAlgebra Q) := inferInstanceAs (IsSemiring (RingQuot (Rel Q)))
instance : IsAlgebra R (CliffordAlgebra Q) := inferInstanceAs (IsAlgebra R (RingQuot (Rel Q)))

instance : Add (CliffordAlgebra Q) := inferInstance
instance : Mul (CliffordAlgebra Q) := inferInstance

end Instances

section Instances

-- a shortcut instance to prevent timeouts
local instance (priority := 5000) [RingOps α] [IsRing α] : IsSemiring α := IsRing.toIsSemiring

variable [RingOps R] [IsRing R] [IsCommMagma R] [AddGroupOps V]
  [IsAddGroup V] [IsAddCommMagma V] [SMul R V] [IsModule R V]

variable (Q: QuadraticForm R V)

instance : RingOps (CliffordAlgebra Q) := RingQuot.instRingOps
instance : IsRing (CliffordAlgebra Q) := inferInstanceAs (IsRing (RingQuot (CliffordAlgebra.Rel Q)))
instance : Sub (CliffordAlgebra Q) := inferInstance
instance : Neg (CliffordAlgebra Q) := inferInstance

end Instances

section ι

variable [SemiringOps R] [IsSemiring R] [IsCommMagma R] [AddMonoidOps V]
  [IsAddMonoid V] [IsAddCommMagma V] [SMul R V] [IsModule R V]

variable (Q: QuadraticForm R V)

namespace CliffordAlgebra

def ofTensorAlgebra :
  TensorAlgebra R V →ₐ[R] CliffordAlgebra Q := RingQuot.mkAlgHom R _

def ι : V →ₗ[R] CliffordAlgebra Q :=
  (ofTensorAlgebra Q).toLinearMap.comp (TensorAlgebra.ι R)

private def algmap_coe_eq
  [SemiringOps A] [SemiringOps B] [AlgebraMap R A] [AlgebraMap R B]
  (f: A →ₐ[R] B) (x: A) : f.toFun x = f x := rfl

/-- As well as being linear, `ι Q` squares to the quadratic form -/
@[simp]
def ι_sq_scalar (v: V) : ι Q v * ι Q v = algebraMap (Q v) := by
  rw [ι]
  dsimp [LinearMap.comp, DFunLike.coe, AlgHom.toLinearMap]
  rw [algmap_coe_eq, ←map_mul (f := ofTensorAlgebra Q)]
  show _ = algebraMap _
  apply (RingQuot.mkAlgHom_rel R (CliffordAlgebra.Rel.intro v)).trans
  apply map_algebraMap

def lift [SMul R A] [SemiringOps A] [AlgebraMap R A] [IsSemiring A] [IsAlgebra R A]  :
    { f : V →ₗ[R] A // ∀ m, f m * f m = algebraMap (Q m) } ≃ (CliffordAlgebra Q →ₐ[R] A) where
  toFun f := RingQuot.liftAlgHom (S := R) ⟨TensorAlgebra.lift R f.val, by
      intro a b r
      induction r with | intro v =>
      rw [map_mul, TensorAlgebra.lift_ι_apply, f.property,
        map_algebraMap]⟩
  invFun f := {
    val := f.toLinearMap.comp (ι Q)
    property := by
      intro v
      rw [LinearMap.comp]
      show f (ι Q v) * f (ι Q v) = _
      rw [←map_mul, ι_sq_scalar, map_algebraMap]
  }
  leftInv f := by
    ext v
    apply (RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _).trans
    apply TensorAlgebra.lift_ι_apply
  rightInv f := by
    simp
    apply RingQuot.ringQuot_ext'
    ext v
    apply (RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _).trans
    apply TensorAlgebra.lift_ι_apply

@[elab_as_elim, induction_eliminator]
def induction {C : CliffordAlgebra Q → Prop}
  (algebraMap: ∀r: R, C (algebraMap r)) (ι: ∀ x, C (ι Q x))
  (mul: ∀ a b, C a → C b → C (a * b)) (add: ∀ a b, C a → C b → C (a + b))
  (a : CliffordAlgebra Q) : C a := by
  obtain ⟨a, rfl⟩  := RingQuot.mkAlgHom_surj R _ a
  induction a with
  | algebraMap =>
    rw [map_algebraMap]
    apply algebraMap
  | ι v => apply ι
  | add =>
    rw [map_add]
    apply add
    assumption
    assumption
  | mul =>
    rw [map_mul]
    apply mul
    assumption
    assumption

end CliffordAlgebra

-- the canonical map from a TensorAlgebra to a CliffordAlgebra
def toClifford : TensorAlgebra R V →ₐ[R] CliffordAlgebra Q :=
  TensorAlgebra.lift R (CliffordAlgebra.ι Q)

@[simp]
theorem toClifford_ι (v: V) : toClifford Q (TensorAlgebra.ι R v) = CliffordAlgebra.ι Q v := by
  simp [toClifford]

end ι

namespace CliffordAlgebra

-- a shortcut instance to prevent timeouts
local instance (priority := 5000) [RingOps α] [IsRing α] : IsSemiring α := IsRing.toIsSemiring

variable
  [RingOps R] [IsRing R] [IsCommMagma R]
  [AddGroupOps V] [IsAddGroup V] [IsAddCommMagma V]
  [SMul R V] [IsModule R V]

def ι_mul_add_comm_mul (Q: QuadraticForm R V) (v w: V) : ι Q v * ι Q w + ι Q w * ι Q v = algebraMap (Q.polar v w) := by
  simp only [QuadraticMap.polar, BilinMap.apply_mk]
  have : (ι Q v + ι Q w) * (ι Q v + ι Q w) =
    (ι Q) v * (ι Q) w + (ι Q) w * (ι Q) v + algebraMap (Q w) + algebraMap (Q v) := by
    simp only [mul_add, add_mul, ι_sq_scalar]
    ac_rfl
  rw [map_sub, map_sub]
  apply add_right_cancel (k := algebraMap (Q w) + algebraMap (Q v))
  rw [←add_assoc, ←add_assoc, sub_add_cancel, sub_add_cancel, ←this, ←map_add, ι_sq_scalar]

end CliffordAlgebra
