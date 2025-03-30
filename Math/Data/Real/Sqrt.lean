import Math.Data.NNReal.Sqrt

namespace Real

noncomputable def sqrt (x: ℝ) : ℝ :=
  NNReal.embedReal (NNReal.sqrt (NNReal.ofReal x))

def sqrt_def (x: ℝ) (hx: 0 ≤ x) : sqrt x = NNReal.embedReal (NNReal.sqrt ⟨x, hx⟩) := by
  unfold sqrt NNReal.ofReal
  conv in max x 0 =>{
    rw (occs := [1]) [max_iff_le_right.mp hx]
  }

def sqrt_sq (x: ℝ) (h: 0 ≤ x) : x.sqrt ^ 2 = x := by
  rw [sqrt_def x h]
  rw [←map_npow, NNReal.sqrt_sq]; rfl

def sqrt_of_sq (x: ℝ) : (x ^ 2).sqrt = |x| := by
  rw [sqrt_def (x^2) (by
    apply Real.square_nonneg x)]
  show NNReal.embedReal (NNReal.sqrt (NNReal.square x)) = _
  rw [NNReal.sqrt_square]
  rfl

def sqrt_of_sq_nonneg (x: ℝ) (hx: 0 ≤ x) : (x ^ 2).sqrt = x := by
  rw [sqrt_of_sq, (abs_of_nonneg _).mp hx]

def sqrt_nonneg (x: ℝ) : 0 ≤ x.sqrt := by apply NNReal.isNonneg

def sqrt_inj {x y: ℝ} (hx: 0 ≤ x) (hy: 0 ≤ y) : x.sqrt = y.sqrt ↔ x = y := by
  unfold sqrt
  apply Iff.trans NNReal.embedReal.inj.eq_iff
  apply Iff.trans (OrderIso.inj _).eq_iff
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
  have := NNReal.geom_mean_le_midpoint (NNReal.square (a * d)) (NNReal.square (b * c))
  rw [←mul_div?_cancel (a := _ + _) (b := 2) (by invert_tactic)]
  apply mul_le_mul_of_nonneg_left
  apply Real.ofRat_le.mpr
  decide
  rw [NNReal.square_mul, NNReal.sqrt_square] at this
  rw [←midpoint]
  replace this : NNReal.embedReal (NNReal.abs ((a * d) * (b * c))) ≤
    NNReal.embedReal (midpoint (NNReal.square (a * d)) (NNReal.square (b * c))) := this
  apply le_trans _ this
  show _ ≤ |(a * d) * (b * c)|
  rw [show (a * d) * (b * c) = a * b * c * d by ac_rfl]
  rw [Real.abs_def]
  split
  rfl
  rw [not_le] at *
  rename_i h
  replace h := le_of_lt h
  apply le_trans h
  rwa [←Real.neg_le_neg_iff, neg_neg]

def sqrt_ne_zero (a: ℝ) (h: 0 < a) : a.sqrt ≠ 0 := by
  intro g
  rw [←map_zero NNReal.embedReal] at g
  have := (NNReal.sqrt_ne_zero _ · (NNReal.embedReal.inj g))
  unfold NNReal.ofReal at this
  replace this := Subtype.mk.inj (Classical.byContradiction this)
  rw [max_def] at this
  split at this
  have := not_le_of_lt h; contradiction
  rw [this] at h
  exact lt_irrefl h

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply sqrt_ne_zero <;> invert_tactic)

end Real
