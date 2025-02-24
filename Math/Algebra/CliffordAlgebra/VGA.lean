import Math.Algebra.QuadraticForm.Signature
import Math.Algebra.CliffordAlgebra.Defs
import Math.Data.Real.Basic

namespace VGA

abbrev Vector (n: ℕ) := Fin n -> ℝ

def QF (n: ℕ) : QuadraticForm ℝ (Vector n) := (QuadraticForm.ofSignature' 0 n 0 n (Nat.zero_add _).symm)

end VGA

def VGA (n: ℕ) := CliffordAlgebra (R := ℝ) (VGA.QF n)

namespace VGA

instance : RingOps (VGA n) := inferInstanceAs (RingOps (CliffordAlgebra _))
instance instRing : IsRing (VGA n) := inferInstanceAs (IsRing (CliffordAlgebra _))
instance : IsSemiring (VGA n) := instRing.toIsSemiring
instance : SMul ℝ (VGA n) := inferInstanceAs (SMul ℝ (CliffordAlgebra _))
instance : IsModule ℝ (VGA n) := inferInstanceAs (IsModule ℝ (CliffordAlgebra _))
instance : AlgebraMap ℝ (VGA n) := inferInstanceAs (AlgebraMap ℝ (CliffordAlgebra _))
instance : IsAlgebra ℝ (VGA n) := inferInstanceAs (IsAlgebra ℝ (CliffordAlgebra _))

def ι : (Vector n) →ₗ[ℝ] VGA n := CliffordAlgebra.ι (R := ℝ) (QF n)
def ι_sq (v: Vector n) : ι v * ι v = algebraMap (QF n v) := CliffordAlgebra.ι_sq_scalar _ _
def ι_mul_add_comm_mul (v w: Vector n) : ι v * ι w + ι w * ι v = algebraMap ((QF n).polar v w) := CliffordAlgebra.ι_mul_add_comm_mul _ _ _

namespace VGA3

def dot (v w: Vector 3) : ℝ := v 0 * w 0 + v 1 * w 1 + v 2 * w 2

def i : Vector 3 := fun i => if i = 0 then 1 else 0
def j : Vector 3 := fun i => if i = 1 then 1 else 0
def k : Vector 3 := fun i => if i = 2 then 1 else 0

def ι_eq_lincomb (v: Vector 3) : ι v = v 0 • ι i + v 1 • ι j + v 2 • ι k := by
  simp only [←resp_smul, ←resp_add]
  congr
  unfold i j k
  ext i
  simp
  match i with
  | 0 =>
    rw [if_pos, if_neg, if_neg]
    simp
    all_goals decide
  | 1 =>
    rw [if_neg, if_pos, if_neg]
    simp
    all_goals decide
  | 2 =>
    rw [if_neg, if_neg, if_pos]
    simp
    all_goals decide

example : ι i * ι j = -ι j * ι i := by
  rw [←neg_mul_left]
  refine neg_eq_of_add_right ?_
  rw [ι_mul_add_comm_mul]
  rfl

@[simp] def i_sq : algebraMap (QF 3 i) = (1: VGA 3) := rfl
@[simp] def j_sq : algebraMap (QF 3 j) = (1: VGA 3) := rfl
@[simp] def k_sq : algebraMap (QF 3 k) = (1: VGA 3) := rfl

@[simp]
def anticomm_ij : ι j * ι i = -(ι i * ι j) := by
  symm
  refine neg_eq_of_add_left ?_
  rw [ι_mul_add_comm_mul]
  rfl
@[simp]
def anticomm_ik : ι k * ι i = -(ι i * ι k) := by
  symm
  refine neg_eq_of_add_left ?_
  rw [ι_mul_add_comm_mul]
  rfl
@[simp]
def anticomm_jk : ι k * ι j = -(ι j * ι k) := by
  symm
  refine neg_eq_of_add_left ?_
  rw [ι_mul_add_comm_mul]
  rfl

def anticomm' (v w: Vector 3) : ι v * ι w = -ι w * ι v + 2 * algebraMap (dot v w) := by
  rw [←neg_mul_left]
  apply add_left_cancel (k := ι w * ι v)
  rw [←add_assoc, add_neg_cancel, zero_add]
  rw [ι_eq_lincomb v, ι_eq_lincomb w]
  simp [smul_add, add_mul, mul_add, i, j, k,
    one_smul, zero_smul, smul_mul,
    ι_sq, smul_one]
  ac_nf
  repeat rw [←add_assoc, smul_neg, neg_add_cancel, zero_add]
  repeat rw [←resp_add]
  rw [←add_assoc, ←two_mul, ←add_assoc (v 1 * _), ←two_mul, ←two_mul]
  rw [←mul_add, ←mul_add, ←add_assoc]
  rw [resp_mul]
  rfl

end VGA3

end VGA
