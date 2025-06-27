import Math.Algebra.CliffordAlgebra.Defs

namespace CliffordAlgebra

section

variable [SemiringOps R] [IsSemiring R] [IsCommMagma R] [AddMonoidOps V]
  [IsAddMonoid V] [IsAddCommMagma V] [SMul R V] [IsModule R V]

variable {Q: QuadraticForm R V}

private def preReverse (Q: QuadraticForm R V) : CliffordAlgebra Q →ₐ[R] (CliffordAlgebra Q)ᵐᵒᵖ :=
  CliffordAlgebra.lift Q {
    val := (LinearEquiv.MulOpp _).toLinearMap.comp (ι Q)
    property := by
      intro m
      simp
      rw [←MulOpp.mk_mul, ι_sq_scalar]
      rfl
  }

private def preReverse_ι : preReverse Q (ι Q v) = MulOpp.mk (ι Q v) := by
  rw [preReverse, lift_ι_apply]
  rfl

private def preReverse_preReverse (c: CliffordAlgebra Q) : (preReverse Q (preReverse Q c).get).get = c := by
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

private def reverseEquiv (Q: QuadraticForm R V) : CliffordAlgebra Q ≃ₐ[R] (CliffordAlgebra Q)ᵐᵒᵖ := {
  preReverse Q with
  invFun := AlgEquiv.mulopp_hom_eqv_hom_mul_opp.symm (preReverse Q)
  leftInv c := by apply preReverse_preReverse
  rightInv c := by apply preReverse_preReverse
}

private def apply_reverseEquiv : reverseEquiv Q c = preReverse Q c := rfl

def reverse (Q: QuadraticForm R V) : CliffordAlgebra Q ≃ₗ[R] CliffordAlgebra Q :=
  (reverseEquiv Q).toLinearEquiv.trans (LinearEquiv.MulOpp _).symm

@[simp]
def reverse_ι : reverse Q (ι Q v) = ι Q v := by
  rw [reverse]
  simp
  rw [apply_reverseEquiv, preReverse_ι]
  rfl

@[simp]
def reverse_algebraMap (r: R) : reverse Q (algebraMap r) = algebraMap r := by
  simp [reverse]
  rw [map_algebraMap]
  rfl

@[simp]
def reverse_mul (a b: CliffordAlgebra Q) : reverse Q (a * b) = reverse Q b * reverse Q a := by
  unfold reverse
  simp
  rw [map_mul]
  rfl

@[simp]
def reverse_add (a b: CliffordAlgebra Q) : reverse Q (a + b) = reverse Q a + reverse Q b := by
  rw [map_add]

@[simp]
def reverse_smul (r: R) (a: CliffordAlgebra Q) : reverse Q (r • a) = r • reverse Q a := by
  rw [map_smul]

def reverse_reverse : Function.IsInvolutive (reverse Q) :=
  (reverseEquiv Q).leftInv

@[simp]
def reverse_symm : (reverse Q).symm = reverse Q := by
  ext a
  symm; show _ = Equiv.symm (reverse Q).toEquiv a; apply Equiv.eq_symm_of_coe_eq
  apply reverse_reverse

attribute [irreducible] reverse

end

section

variable [RingOps R] [IsRing R] [IsCommMagma R] [AddGroupOps V]
  [IsAddGroup V] [IsAddCommMagma V] [SMul R V] [IsModule R V]

variable {Q: QuadraticForm R V}

private def preInvolute (Q: QuadraticForm R V) : { f: V →ₗ[R] CliffordAlgebra Q // ∀ (m : V), f m * f m = algebraMap (Q m) } where
  val := -CliffordAlgebra.ι Q
  property v := by
    rw [LinearMap.apply_neg, neg_mul, mul_neg,
      neg_neg, ι_sq_scalar]

def involute (Q: QuadraticForm R V) : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q := {
  lift Q (preInvolute Q), Equiv.ofInvolut (lift Q (preInvolute Q)) (by
    intro x
    induction x with
    | algebraMap x => rw [map_algebraMap, map_algebraMap]
    | add a b iha ihb => rw [map_add, map_add, iha, ihb]
    | mul a b iha ihb => rw [map_mul, map_mul, iha, ihb]
    | ι x =>
      rw [lift_ι_apply]
      show lift Q _ (-ι Q x) = _
      rw [map_neg, lift_ι_apply]
      apply neg_neg) with
}

@[simp]
def involute_ι (v: V) : involute Q (ι Q v) = -ι Q v := by
  show lift Q (preInvolute Q) _ = _
  rw [lift_ι_apply]
  rfl

@[simp]
def involute_algebraMap (r: R) : involute Q (algebraMap r) = algebraMap r := by
  rw [map_algebraMap]

@[simp]
def involute_add (a b: CliffordAlgebra Q) : involute Q (a + b) = involute Q a + involute Q b := by
  rw [map_add]

@[simp]
def involute_mul (a b: CliffordAlgebra Q) : involute Q (a * b) = involute Q a * involute Q b := by
  rw [map_mul]

@[simp]
def involute_involute (x: CliffordAlgebra Q) : involute Q (involute Q x) = x := by
  apply (involute Q).leftInv

def involute_comp_involute : (involute Q).trans (involute Q) = AlgEquiv.refl := by
  ext x; simp

@[simp]
def involute_symm : (involute Q).symm = involute Q := by
  ext a
  symm; show _ = Equiv.symm (involute Q).toEquiv a; apply Equiv.eq_symm_of_coe_eq
  apply involute_involute

def reverse_involute_comm (a: CliffordAlgebra Q) : reverse Q (involute Q a) = involute Q (reverse Q a) := by
  induction a with
  | algebraMap => simp
  | ι => simp [map_neg]
  | add _ _ ih₀ ih₁ => simp [ih₀, ih₁]
  | mul _ _ ih₀ ih₁ => simp [ih₀, ih₁]

def reverse_trans_involute_comm : (reverse Q).trans (involute Q).toLinearEquiv = (involute Q).toLinearEquiv.trans (reverse Q) := by
  ext; symm; apply reverse_involute_comm

attribute [irreducible] involute

def conj (Q: QuadraticForm R V) : CliffordAlgebra Q ≃ₗ[R] CliffordAlgebra Q :=
  (involute Q).toLinearEquiv.trans (reverse Q)

@[simp]
def conj_ι : conj Q (ι Q v) = -ι Q v := by
  simp [conj, map_neg]

@[simp]
def conj_algebraMap (r: R) : conj Q (algebraMap r) = algebraMap r := by
  simp [conj]

@[simp]
def conj_mul (a b: CliffordAlgebra Q) : conj Q (a * b) = conj Q b * conj Q a := by
  simp [conj]

@[simp]
def conj_add (a b: CliffordAlgebra Q) : conj Q (a + b) = conj Q a + conj Q b := by
  simp [conj]

@[simp]
def conj_smul (r: R) (a: CliffordAlgebra Q) : conj Q (r • a) = r • conj Q a := by
  rw [map_smul]

def conj_eq_involute_reverse : conj Q = (involute Q).toLinearEquiv.trans (reverse Q) := rfl

@[simp]
def symm_conj : (conj Q).symm = conj Q := by
  simp [conj_eq_involute_reverse, reverse_trans_involute_comm]
  rw [←reverse_trans_involute_comm]
  congr
  show (involute Q).symm.toLinearEquiv = _
  simp

def conj_conj : Function.IsInvolutive (conj Q) := by
  intro a; rw (occs := [1]) [←symm_conj, LinearEquiv.coe_symm]

attribute [irreducible] conj

end

end CliffordAlgebra
