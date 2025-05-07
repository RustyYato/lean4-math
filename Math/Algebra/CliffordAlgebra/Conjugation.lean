import Math.Algebra.CliffordAlgebra.Defs

namespace CliffordAlgebra

section

variable [RingOps R] [IsRing R] [IsCommMagma R] [AddGroupOps V]
  [IsAddGroup V] [IsAddCommMagma V] [SMul R V] [IsModule R V]

variable {Q: QuadraticForm R V}

private def preInvolute (Q: QuadraticForm R V) : { f: V →ₗ[R] CliffordAlgebra Q // ∀ (m : V), f m * f m = algebraMap (Q m) } where
  val := -CliffordAlgebra.ι Q
  property v := by
    rw [LinearMap.apply_neg, neg_mul, mul_neg,
      neg_neg, ι_sq_scalar]

def involute (Q: QuadraticForm R V) : CliffordAlgebra Q →ₐ[R] CliffordAlgebra Q :=
  lift Q (preInvolute Q)

def involute_ι (v: V) : involute Q (ι Q v) = -ι Q v := by
  rw [involute, lift_ι_apply]
  rfl

@[simp]
def involute_involute (x: CliffordAlgebra Q) : involute Q (involute Q x) = x := by
  induction x with
  | algebraMap x => rw [map_algebraMap, map_algebraMap]
  | add a b iha ihb => rw [map_add, map_add, iha, ihb]
  | mul a b iha ihb => rw [map_mul, map_mul, iha, ihb]
  | ι x => rw [involute_ι, map_neg, involute_ι, neg_neg]

def involute_comp_involute : (involute Q).comp (involute Q) = AlgHom.id _ := by
  ext x; simp

def preReverse (Q: QuadraticForm R V) : CliffordAlgebra Q →ₐ[R] (CliffordAlgebra Q)ᵐᵒᵖ :=
  CliffordAlgebra.lift Q {
    val := (LinearEquiv.MulOpp _).toLinearMap.comp (ι Q)
    property := by
      intro m
      simp
      rw [←MulOpp.mk_mul, ι_sq_scalar]
      rfl
  }

def preReverse_ι : preReverse Q (ι Q v) = MulOpp.mk (ι Q v) := by
  rw [preReverse, lift_ι_apply]
  rfl

def preReverse_preReverse (c: CliffordAlgebra Q) : (preReverse Q (preReverse Q c).get).get = c := by
  induction c with
  | algebraMap c =>
    simp [map_algebraMap]
    let a: CliffordAlgebra Q := algebraMap c
    show (preReverse Q a).get = algebraMap c
    rw [map_algebraMap]
    rfl
  | add _ _ ih₀ ih₁ => simp [map_add, ih₀, ih₁]
  | mul _ _ ih₀ ih₁ => simp [map_mul, ih₀, ih₁]
  | ι =>
    rw [preReverse_ι]
    show preReverse Q (ι Q _) = _
    rw [preReverse_ι]; rfl

def reverseEquiv (Q: QuadraticForm R V) : CliffordAlgebra Q ≃ₐ[R] (CliffordAlgebra Q)ᵐᵒᵖ := {
  preReverse Q with
  invFun := AlgEquiv.mulopp_hom_eqv_hom_mul_opp.symm (preReverse Q)
  leftInv c := by apply preReverse_preReverse
  rightInv c := by apply preReverse_preReverse
}

def apply_reverseEquiv : reverseEquiv Q c = preReverse Q c := rfl

def reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q :=
  (LinearEquiv.MulOpp _).symm.toLinearMap.comp (reverseEquiv Q).toLinearMap

@[simp]
def reverse_ι : reverse (ι Q v) = ι Q v := by
  rw [reverse]
  simp
  rw [apply_reverseEquiv, preReverse_ι]
  rfl

@[simp]
def reverse_algebraMap (r: R) : reverse (Q := Q) (algebraMap r) = algebraMap r := by
  rw [reverse]
  simp
  rw [map_algebraMap]
  rfl

@[simp]
def reverse_mul (a b: CliffordAlgebra Q) : reverse (a * b) = reverse b * reverse a := by
  unfold reverse
  simp
  rw [map_mul]
  rfl

@[simp]
def reverse_add (a b: CliffordAlgebra Q) : reverse (a + b) = reverse a + reverse b := by
  rw [map_add]

@[simp]
def reverse_smul (r: R) (a: CliffordAlgebra Q) : reverse (r • a) = r • reverse a := by
  rw [map_smul]

end

end CliffordAlgebra
