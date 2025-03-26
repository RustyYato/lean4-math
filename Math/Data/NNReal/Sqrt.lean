import Math.Data.NNReal.Pow

namespace NNReal

noncomputable def sqrt : ℝ≥0 -> ℝ≥0 :=
  (NNReal.npowOrderIso 2 (by decide)).symm

def sqrt_sq (x: ℝ≥0) : x.sqrt ^ 2 = x :=
  (NNReal.npowOrderIso 2 (by decide)).symm_coe _

def sqrt_of_sq (x: ℝ≥0) : (x ^ 2).sqrt = x :=
  (NNReal.npowOrderIso 2 (by decide)).coe_symm _

def sqrt_inj {x y: ℝ≥0} : x.sqrt = y.sqrt ↔ x = y :=
  (NNReal.npowOrderIso 2 (by decide)).symm.inj.eq_iff

def sqrt_surj {x: ℝ≥0} : ∃y: ℝ≥0, y.sqrt = x := by
  exists x ^ 2
  rw [sqrt_of_sq]

def sqrt_strictMonotone : StrictMonotone sqrt := by
  intro x y h
  apply (NNReal.npowOrderIso 2 (by decide)).symm.resp_lt.mp
  assumption

@[simp]
def sqrt_0 : sqrt 0 = 0 := by
  rw (occs := [2]) [←sqrt_of_sq 0]
  rfl
@[simp]
def sqrt_1 : sqrt 1 = 1 := by
  rw (occs := [2]) [←sqrt_of_sq 1]
  rfl

def square_strictMonotone : StrictMonotone (α := ℝ≥0) (· ^ 2) :=
  npowStrictMono 2 (by decide)

noncomputable def npowEquiv (n: ℕ) (h: 0 < n) : ℝ≥0 ≃*₀ ℝ≥0 := {
  (NNReal.npowOrderIso n h), (npowHom₀ n h)  with
}

noncomputable def sqrtEquiv : ℝ≥0 ≃*₀ ℝ≥0 := (npowEquiv 2 (by decide)).symm

def apply_sqrtEquiv (x: ℝ≥0) : sqrtEquiv x = sqrt x := rfl

def abs (r: ℝ) : ℝ≥0 where
  val := ‖r‖
  property := by apply abs_nonneg (α := ℝ)

def square (r: ℝ) : ℝ≥0 where
  val := r ^ 2
  property := by
    rw [Real.mem_nonneg, npow_two]
    exact Real.square_nonneg r

@[simp] def square_zero : square 0 = 0 := rfl
@[simp] def square_one : square 1 = 1 := rfl

def square_sub_comm (a b: ℝ) : square (a - b) = square (b - a) := by
  apply embedReal.inj
  show (a - _) ^ 2 = (_ - _) ^ 2
  rw [←square_neg, neg_sub]

def square_neg (a: ℝ) : square (-a) = square a := by
  apply embedReal.inj
  show (-_) ^ 2 = a ^ 2
  rw [_root_.square_neg]

def mk (x: ℝ) (h: 0 ≤ x) : ℝ≥0 := ⟨x, h⟩

def sqrt_square (r: ℝ) : sqrt (square r) = abs r := by
  rcases le_total 0 r with h | h
  rw [show (square r) = (mk r h) ^ 2 from rfl]
  rw [sqrt_of_sq, abs, mk]
  congr; rw [(Real.abs_of_nonneg _).mp h]
  rw [←square_neg]; rw [←Real.neg_le_neg_iff] at h
  rw [show (square (-r)) = (mk (-r) h) ^ 2 from rfl]
  rw [sqrt_of_sq]
  unfold abs mk
  congr
  rw [←abs_neg, (Real.abs_of_nonneg _).mp h]

def of_square_eq_zero : square r = 0 -> r = 0 := by
  intro h
  have : sqrt (square r) = 0 := by simp [h]
  rw [sqrt_square] at this
  exact of_abs_eq_zero (Subtype.mk.inj this)

def sqrt_mul (a b: ℝ≥0) : a.sqrt * b.sqrt = (a * b).sqrt := by
  symm; apply resp_mul sqrtEquiv

def geom_mean_le_midpoint (a b: ℝ≥0) : sqrt (a * b) ≤ midpoint a b := by
  apply square_strictMonotone.le_iff_le.mp
  rw [sqrt_sq, midpoint, div?_npow, square_add,
    add_comm (a^2), add_assoc, ←add_div?_add₀,
      mul_assoc, mul_comm 2]
  have : 2 /? (2^2: ℝ≥0) = 2⁻¹? := by
    symm; apply inv?_eq_of_mul_left
    rw [div?_eq_mul_inv?, ←mul_assoc, ←npow_two, mul_inv?_cancel]
  rw [div?_eq_mul_inv?, mul_assoc (a * b), ←div?_eq_mul_inv?, this, ←div?_eq_mul_inv?]

  -- show a * b ≤ (a * b) /? 2 + _
  sorry

end NNReal
