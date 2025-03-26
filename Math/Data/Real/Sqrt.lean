import Math.Data.NNReal.Pow

namespace Real

noncomputable def sqrt (x: ℝ) : ℝ :=
  NNReal.embedReal ((NNReal.npowOrderIso 2 (by decide)).symm (NNReal.ofReal x))

def sqrt_sq (x: ℝ) (h: 0 ≤ x) : x.sqrt ^ 2 = x := by
  unfold sqrt
  let e := NNReal.npowOrderIso 2 (by decide)
  have := e.coe_symm (NNReal.ofReal x)
  rw [←resp_npow]
  show NNReal.embedReal (e (e.symm _)) = x
  rw [e.symm_coe, NNReal.ofReal_embedReal]
  assumption

def sqrt_of_sq (x: ℝ) : (x ^ 2).sqrt = ‖x‖ := by
  unfold sqrt
  conv in NNReal.ofReal _ => {
    unfold NNReal.ofReal
    arg 1
    rw [max_iff_le_right.mp (by
      rw [npow_two]
      apply square_nonneg)]
  }
  let e := NNReal.npowOrderIso 2 (by decide)
  rcases le_total 0 x with hx | hx
  show NNReal.embedReal (e.symm (e ⟨x, hx⟩)) = ‖x‖
  rw [e.coe_symm, (Real.abs_of_nonneg _).mp hx]; rfl
  conv in x^2 => {
    rw [show x^2 = (-x)^2 by
      rw [npow_two, npow_two, ←neg_mul_right, ←neg_mul_left, neg_neg]]
  }
  rw [←Real.neg_le_neg_iff] at hx
  show NNReal.embedReal (e.symm (e ⟨-x, hx⟩)) = ‖x‖
  rw [e.coe_symm, ←abs_neg, (Real.abs_of_nonneg _).mp hx]; rfl

def sqrt_of_sq_nonneg (x: ℝ) (hx: 0 ≤ x) : (x ^ 2).sqrt = x := by
  rw [sqrt_of_sq, (abs_of_nonneg _).mp hx]

def sqrt_nonneg (x: ℝ) : 0 ≤ x.sqrt := by apply NNReal.isNonneg

def sqrt_inj {x y: ℝ} (hx: 0 ≤ x) (hy: 0 ≤ y) : x.sqrt = y.sqrt ↔ x = y := by
  unfold sqrt
  rw [NNReal.embedReal.inj.eq_iff, (OrderIso.inj _).eq_iff]
  unfold NNReal.ofReal
  apply Iff.intro
  intro h
  have := Subtype.mk.inj h
  rwa [max_iff_le_right.mp, max_iff_le_right.mp] at this
  assumption
  assumption
  intro h
  rw [h]

def sqrt_surj {x: ℝ} (hx: 0 ≤ x) : ∃y: ℝ, y.sqrt = x := by
  exists x ^ 2
  rwa [sqrt_of_sq_nonneg]

def sqrt_monotone : Monotone sqrt := by
  intro x y h
  show NNReal.orderEmbedReal _ ≤ NNReal.orderEmbedReal _
  apply (OrderEmbedding.resp_le _).mp
  apply (OrderIso.resp_le _).mp
  unfold NNReal.ofReal
  show max x 0 ≤ max y 0
  rw [le_max_iff, max_le_iff, max_le_iff]
  simp
  rcases le_total x 0
  right; assumption
  left
  apply And.intro
  assumption
  apply le_trans _ h
  assumption

def sqrt_strictMonotoneOn : StrictMonotoneOn sqrt (Set.Ici 0) := by
  intro x y hx hy h
  rw [Set.mem_Ici] at hx hy
  show NNReal.orderEmbedReal _ < NNReal.orderEmbedReal _
  apply (OrderEmbedding.resp_lt _).mp
  apply (OrderIso.resp_lt _).mp
  unfold NNReal.ofReal
  show max x 0 < max y 0
  rwa [max_iff_le_right.mp hx, max_iff_le_right.mp hy]

@[simp]
def sqrt_0 : sqrt 0 = 0 := by
  rw (occs := [2]) [←abs_zero (α := ℝ)]
  rw [←sqrt_of_sq]
  rfl
@[simp]
def sqrt_1 : sqrt 1 = 1 := by
  rw (occs := [2]) [←abs_one (α := ℝ)]
  rw [←sqrt_of_sq]
  rfl

def npow_strictMonotoneOn (n: ℕ) (h: 0 < n) : StrictMonotoneOn (α := ℝ) (· ^ n) (Set.Ici 0) := by
  intro x y hx hy h
  simp
  let x' : ℝ≥0 := ⟨x, hx⟩
  let y' : ℝ≥0 := ⟨y, hy⟩
  show x' ^ n < y' ^ n
  apply NNReal.npowStrictMono
  assumption
  assumption

def square_strictMonotoneOn : StrictMonotoneOn (α := ℝ) (· ^ 2) (Set.Ici 0) :=
  npow_strictMonotoneOn 2 (by decide)

def cauchy_schwartz (a b c d: ℝ) : (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  simp [npow_two, mul_add, add_mul]
  ac_nf
  apply add_le_add_left
  rw [←add_assoc, ←add_assoc]
  apply add_le_add_right
  repeat rw [←mul_assoc]
  rw [←two_mul]
  rw [←npow_two, mul_assoc (_^2), ←npow_two]
  rw [←npow_two, mul_assoc (_^2), ←npow_two]
  rw [←mul_npow, ←mul_npow]
  sorry


end Real
