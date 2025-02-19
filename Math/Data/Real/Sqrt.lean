import Math.Data.Real.Order
import Math.Data.Rat.Basic
import Math.Data.Real.Div

noncomputable def Real.sqrt : ℝ -> ℝ :=
  Function.invFun_on (Set.mk fun x => 0 ≤ x) (fun a => a * a)

def Real.sqrt_of_sq_of_nonneg (a: ℝ) (h: 0 ≤ a): Real.sqrt (a * a) = a := by
  apply Function.invFun_eq'_on (f := fun a: ℝ => a * a) _ h
  intro a b ha hb eq
  rw [Set.mk_mem] at ha hb
  dsimp at eq
  rcases lt_trichotomy a b with h | h | h
  have := Real.mul_lt_mul_of_nonneg ha ha h h
  rw [eq] at this; have := lt_irrefl this; contradiction
  assumption
  have := Real.mul_lt_mul_of_nonneg hb hb h h
  rw [eq] at this; have := lt_irrefl this; contradiction

def Real.sqrt_of_sq (a: ℝ): Real.sqrt (a * a) = ‖a‖ := by
  rw [abs_def]
  split
  rw [sqrt_of_sq_of_nonneg]
  assumption
  rw [←neg_neg (a * a), neg_mul_left, neg_mul_right, sqrt_of_sq_of_nonneg]
  rw [←neg_le_neg_iff, neg_neg]
  apply le_of_lt
  apply lt_of_not_le
  assumption

def Real.sq_sqrt (a: ℝ) (h: 0 ≤ a): Real.sqrt a * Real.sqrt a = a := by
  apply Function.invFun_eq_on (f := fun a: ℝ => a * a)
  exists a.sqrt
  apply And.intro sorry
  sorry

def Real.sqrt_surj (b: ℝ) (hb: 0 ≤ b) : ∃a, 0 ≤ a ∧ Real.sqrt a = b := by
  exists b * b
  apply And.intro
  apply mul_nonneg <;> assumption
  rw [sqrt_of_sq_of_nonneg _ hb]

def Real.sqrt_nonneg (a: ℝ) (ha: 0 ≤ a) : 0 ≤ a.sqrt := by
  sorry

noncomputable def Real.sqrt_order_hom : { x: ℝ // 0 ≤ x } →o ℝ where
  toFun x := Real.sqrt x
  resp_rel := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ ab
    dsimp
    sorry

def Real.sq_surj (b: ℝ) (hb: 0 ≤ b) : ∃a, 0 ≤ a ∧ a * a = b := by
  sorry

def Real.sqrt_inj (a b: ℝ) (ha: 0 ≤ a) (hb: 0 ≤ b) : Real.sqrt a = Real.sqrt b -> a = b := by
  intro h
  have : a.sqrt * a.sqrt = b.sqrt * b.sqrt := by rw [h]
  rw [Real.sq_sqrt _ ha, Real.sq_sqrt _ hb] at this
  assumption
