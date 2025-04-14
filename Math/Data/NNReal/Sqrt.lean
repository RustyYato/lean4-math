import Math.Data.NNReal.Pow
import Math.Algebra.GroupWithZero.Order

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
  apply (map_lt (NNReal.npowOrderIso 2 (by decide)).symm).mp
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
  val := |r|
  property := by apply abs_nonneg (α := ℝ)

def square (r: ℝ) : ℝ≥0 where
  val := r ^ 2
  property := by
    rw [Real.mem_nonneg]
    exact square_nonneg r

@[simp] def embedReal_abs (x: ℝ) : embedReal (abs x) = |x| := rfl
@[simp] def embedReal_square (x: ℝ) : embedReal (square x) = x ^ 2 := rfl

@[simp] def square_zero : square 0 = 0 := rfl
@[simp] def square_one : square 1 = 1 := rfl
def square_eq_abs_sq (x: ℝ): square x = (abs x) ^ 2 := by
  classical
  apply embedReal.inj
  show x ^ 2 = |x| ^ 2
  rw [abs_def]
  split
  rfl
  rw [square_neg]

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
  congr; rw [abs_of_nonneg _ h]
  rw [←square_neg]; rw [neg_le_neg_iff] at h
  rw [show (square (-r)) = (mk (-r) h) ^ 2 from rfl]
  rw [sqrt_of_sq]
  unfold abs mk
  congr
  rw [←abs_neg, abs_of_nonneg _ h]

def of_square_eq_zero : square r = 0 -> r = 0 := by
  intro h
  have : sqrt (square r) = 0 := by simp [h]
  rw [sqrt_square] at this
  exact of_abs_eq_zero (Subtype.mk.inj this)

def square_mul (a b: ℝ) : square a * square b = square (a * b) := by
  apply Subtype.val_inj
  symm; apply mul_npow

def ofReal_square (x: ℝ) : ofReal (x ^ 2) = square x := by
  unfold ofReal
  congr
  rw [max_eq_left.mpr]
  apply square_nonneg

def sqrt_mul (a b: ℝ≥0) : a.sqrt * b.sqrt = (a * b).sqrt := by
  symm; apply map_mul sqrtEquiv

noncomputable def sqrtHom : ℝ≥0 ↪*₀ ℝ≥0 where
  toFun := sqrt
  map_zero := by simp
  map_one := by simp
  map_mul := (sqrt_mul _ _).symm
  inj' := sqrt_strictMonotone.Injective

def geom_mean_le_midpoint (a b: ℝ≥0) : sqrt (a * b) ≤ midpoint a b := by
  apply square_strictMonotone.le_iff_le.mp
  rw [sqrt_sq, midpoint, div?_npow, square_add,
    add_comm (a^2), add_assoc, ←add_div?_add₀,
      mul_assoc, mul_comm 2]
  have : 2 /? (2^2: ℝ≥0) = 2⁻¹? := by
    symm; apply inv?_eq_of_mul_left
    rw [div?_eq_mul_inv?, ←mul_assoc, ←npow_two, mul_inv?_cancel]
  rw [div?_eq_mul_inv?, mul_assoc (a * b), ←div?_eq_mul_inv?, this, ←div?_eq_mul_inv?]
  clear this
  rw (occs := [1]) [←add_half (a * b)]
  apply add_le_add_left
  apply le_of_mul_le_mul_right₀ (c := 4)
  invert_tactic
  show (a * b) /? 2 * (2 * 2) ≤ _ /? 4 * 4
  rw [←mul_assoc, div?_mul_cancel, div?_mul_cancel]
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  show a * b * 2 ≤ a ^2 + b^2
  apply le_of_add_le_add_right (a := _) (b := _) (c := -(a * b * 2))
  rw [add_neg_cancel, add_comm_right, ←sub_eq_add_neg,
    mul_comm, ←mul_assoc, ←square_sub]
  apply square_nonneg

def sqrt_pos (a: ℝ≥0) (h: 0 < a) : 0 < a.sqrt := by
  rw [←sqrt_0]
  apply sqrt_strictMonotone
  assumption

def sqrt_ne_zero (a: ℝ≥0) (h: a ≠ 0) : a.sqrt ≠ 0 := by
  intro g; apply h
  symm; apply (lt_or_eq_of_le (bot_le a)).resolve_left
  clear h; intro h
  have := sqrt_pos _ h
  rw [g] at this
  exact lt_irrefl this

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply sqrt_ne_zero <;> invert_tactic)

def sqrt_eq_zero_iff_eq_zero {a: ℝ≥0} :
  a.sqrt = 0 ↔ a = 0 := by
  apply Iff.intro
  intro h
  rw [←sqrt_0] at h
  exact sqrt_inj.mp h
  rintro rfl
  simp

def abs_eq_zero_iff_eq_zero {a: ℝ} :
  abs a = 0 ↔ a = 0 := by
  apply Iff.intro
  intro h
  apply of_abs_eq_zero
  exact Subtype.mk.inj h
  rintro rfl
  unfold abs
  congr; rw [abs_zero]

def square_eq_zero_iff_eq_zero {a: ℝ} :
  square a = 0 ↔ a = 0 := by
  rw [←NNReal.sqrt_eq_zero_iff_eq_zero]
  rw [sqrt_square, abs_eq_zero_iff_eq_zero]

def sqrt_inv? (a: ℝ≥0) (h: a ≠ 0) : (a⁻¹?).sqrt = a.sqrt⁻¹? :=
  map_inv? sqrtHom _ _
def sqrt_div? (a b: ℝ≥0) (h: b ≠ 0) : (a /? b).sqrt = a.sqrt /? b.sqrt :=
  map_div? sqrtHom _ _ _

end NNReal
