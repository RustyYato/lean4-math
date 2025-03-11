import Math.Data.Real.Order
import Math.Algebra.Field.Basic
import Math.Algebra.QAlgebra.Defs

def CauchySeq.inv.spec_pos (a b: CauchySeq) (ha: a.IsPos) : a ≈ b ->
  is_cauchy_equiv (fun n => if h:a n = 0 then 0 else (a n)⁻¹?) (fun n => if h:b n = 0 then 0 else (b n)⁻¹?) := by
  intro ab ε ε_pos
  have hb := IsPos.spec  _ _ ab ha
  obtain ⟨A, A_pos, ha⟩ := ha
  obtain ⟨B, B_pos, hb⟩ := hb
  simp
  obtain ⟨δ, prf⟩ := ha.to₂_left.merge <| hb.to₂_right.merge (ab _ (Rat.mul_pos ε_pos (Rat.mul_pos (Rat.half_pos A_pos) (Rat.half_pos B_pos))))
  refine ⟨δ, ?_⟩
  intro n m δn δm
  have ⟨A_le_an, B_le_bm, eqv⟩ := prf _ _ δn δm
  have : a n ≠ 0 := by
    intro h
    rw [h] at A_le_an
    exact lt_irrefl (lt_of_le_of_lt A_le_an A_pos)
  have : b m ≠ 0 := by
    intro h
    rw [h] at B_le_bm
    exact lt_irrefl (lt_of_le_of_lt B_le_bm B_pos)
  rw [dif_neg, dif_neg]
  rw [inv_sub_inv, Rat.abs_div?]
  rw [abs_sub_comm]
  by_cases h:a n - b m = 0
  erw [h, div?_eq_mul_inv?, zero_mul]
  assumption
  apply (Rat.lt_iff_mul_right_pos _).mpr
  apply lt_trans _ eqv
  · assumption
  · assumption
  · rw [div?_eq_mul_inv?, mul_assoc]
    apply Rat.pos_mul_lt_of_right_lt_one
    apply Rat.abs_pos
    assumption
    rw [←Rat.abs_inv?, inv?_mul_rev, Rat.abs_mul,
      ←Rat.abs_of_pos _ (Rat.half_pos A_pos), ←Rat.abs_of_pos _ (Rat.half_pos B_pos)]
    suffices ‖A/?2‖ *‖(a n)⁻¹?‖ * (‖B/?2‖ * ‖(b m)⁻¹?‖) < 1 by
      apply lt_of_le_of_lt _ this
      assumption
      assumption
      apply le_of_eq
      ac_rfl
    rw [←Rat.abs_mul, ←Rat.abs_mul, ←div?_eq_mul_inv?, ←div?_eq_mul_inv?]
    conv => { rhs; rw [←mul_one 1] }
    apply Rat.mul_lt_mul
    · apply Rat.abs_pos
      have : A ≠ 0 := by symm; apply ne_of_lt; assumption
      invert_tactic
    · apply (Rat.abs_div_lt_one _ _ _).mpr
      rw [Rat.abs_of_pos, Rat.abs_of_pos]
      apply lt_of_lt_of_le _ A_le_an
      apply Rat.half_lt
      assumption
      apply lt_of_lt_of_le A_pos A_le_an
      apply Rat.half_pos
      assumption
    · apply Rat.abs_pos
      have : B ≠ 0 := by symm; apply ne_of_lt; assumption
      invert_tactic
    · apply (Rat.abs_div_lt_one _ _ _).mpr
      rw [Rat.abs_of_pos, Rat.abs_of_pos]
      apply lt_of_lt_of_le _ B_le_bm
      apply Rat.half_lt
      assumption
      apply lt_of_lt_of_le B_pos B_le_bm
      apply Rat.half_pos
      assumption
  · apply Rat.mul_pos <;> apply Rat.half_pos <;> assumption

def CauchySeq.inv.spec (a b: CauchySeq) (ha: ¬a ≈ 0) : a ≈ b ->
  is_cauchy_equiv (fun n => if h:a n = 0 then 0 else (a n)⁻¹?) (fun n => if h:b n = 0 then 0 else (b n)⁻¹?) := by
  intro ab ε ε_pos
  simp
  rcases pos_or_neg_of_abs_pos (abs_pos_of_non_zero ha) with apos | aneg
  apply inv.spec_pos
  assumption
  assumption
  assumption
  have ⟨δ, prf⟩: Eventually₂ fun n m => ‖(if h : (-a).seq n = 0 then 0 else ((-a).seq n)⁻¹?) - if h : (-b).seq m = 0 then 0 else ((-b).seq m)⁻¹?‖ < ε := by
    apply inv.spec_pos
    assumption
    apply Quotient.exact
    show -Real.mk a = -Real.mk b
    congr 1
    exact Quotient.sound ab
    assumption
  refine ⟨δ, ?_⟩
  intro n m δn δm
  replace prf := prf n m δn δm
  simp at prf
  apply lt_of_le_of_lt _ prf
  clear prf
  rw [←neg_abs]
  apply le_of_eq
  congr
  split <;> split
  · rw [dif_pos, dif_pos]
    rfl
    rename_i h
    rw [h]; rfl
    rename_i h _
    rw [h]; rfl
  · rw [dif_pos, dif_neg]
    rw [sub_eq_add_neg, neg_inv?, sub_neg, zero_add, neg_neg, zero_add]
    invert_tactic
    rename_i h _; rw [h]; rfl
  · rw [dif_neg, dif_pos]
    rw [sub_zero, sub_zero, neg_inv?]
    rename_i h; rw [h]; rfl
    invert_tactic
  · rw [dif_neg, dif_neg]
    rw [neg_inv?, neg_inv?, neg_sub, neg_sub_neg]
    invert_tactic
    invert_tactic

def CauchySeq.inv (a: CauchySeq) (ha: ¬a ≈ 0) : CauchySeq where
  seq n := if h:a n = 0 then 0 else (a n)⁻¹?
  is_cacuhy := by
    apply CauchySeq.inv.spec
    assumption
    rfl

instance : CheckedInvert CauchySeq (fun x => ¬x ≈ 0) := ⟨.inv⟩

def CauchySeq.eventually_pointwise_ne_of_ne (a b: CauchySeq) (h: ¬a ≈ b) : Eventually (fun n => a n ≠ b n) := by
  have : IsPos ‖a - b‖ := CauchySeq.abs_pos_of_non_zero (by
    intro g; apply h
    apply Quotient.exact
    replace g : Real.mk a - Real.mk b = 0 := Quotient.sound g
    exact eq_of_sub_eq_zero (α := ℝ) g)
  obtain ⟨B, B_pos, δ, even⟩ := this
  refine ⟨δ, ?_⟩
  intro n δn
  intro g
  simp at even
  replace even : B ≤ ‖a n - b n‖ := even _ δn
  rw [←g, sub_self] at even
  have := not_lt_of_le even
  contradiction

namespace Real

local instance : Coe ℚ ℝ := ⟨.ofRat⟩

def inv (a: ℝ) : a ≠ 0 -> ℝ := by
  apply a.hrecOn (motive := fun a => a ≠ (0: ℝ) -> ℝ)
  case f =>
    intro a eq
    refine ⟦a.inv ?_⟧
    intro g
    apply eq
    apply Quotient.sound
    assumption
  case c =>
    intro a b eqv
    apply Function.hfunext
    rw [Quotient.sound eqv]
    intro ha hb eq
    apply heq_of_eq
    apply Quotient.sound
    apply CauchySeq.inv.spec
    intro g
    apply ha
    apply Quotient.sound
    assumption
    assumption

instance : CheckedInv? ℝ := ⟨.inv⟩

instance : CheckedDiv? ℝ where
  checked_div a b h := a * b⁻¹?

instance : Min ℝ where
  min x y := (x + y - ‖x - y‖) /? 2
instance : Max ℝ where
  max x y := (x + y + ‖x - y‖) /? 2

def inv_self_mul (a: ℝ) (h: a ≠ 0) : a⁻¹? * a = 1 := by
  induction a using ind with | mk a =>
  apply Quotient.sound
  apply CauchySeq.eventually_pointwise
  have ⟨δ, prf⟩ := CauchySeq.eventually_pointwise_ne_of_ne a 0 (by
    intro g; apply h
    apply Quotient.sound; assumption)
  refine ⟨δ, ?_⟩
  intro n δn
  replace prf : a n ≠ 0 := prf _ δn
  unfold CauchySeq.inv
  simp
  rw [dif_neg prf]
  rw [inv?_mul_cancel]
  rfl

def mul_inv_self (a: ℝ) (h: a ≠ 0) : a * a⁻¹? = 1 := by
  rw [mul_comm, inv_self_mul]

def inv_pos (a: ℝ) (apos: a.IsPos) : (a⁻¹?).IsPos := by
  induction a using ind with | mk a =>
  obtain ⟨B, B_pos, δ, apos⟩ := apos
  have ⟨bound, one_le_bound, prf⟩  := a.upper_bound_with 1
  have bound_pos: 0 < (bound: ℚ) := lt_of_lt_of_le (by decide) one_le_bound
  refine ⟨_, (Rat.inv_pos _ ?_).mp bound_pos, δ, ?_⟩
  intro h; subst h; contradiction
  intro n δn
  have anpos := lt_of_lt_of_le B_pos (apos n δn)
  have := (ne_of_lt bound_pos).symm
  have := (ne_of_lt anpos).symm
  simp at apos
  unfold CauchySeq.inv
  simp
  rw [dif_neg]
  apply (Rat.le_iff_mul_left_pos anpos).mpr
  apply (Rat.le_iff_mul_left_pos bound_pos).mpr
  rw [mul_inv?_cancel, ←mul_assoc, mul_comm bound, mul_assoc, mul_inv?_cancel,
    mul_one, mul_one]
  apply le_of_lt
  apply prf
  assumption

def of_mul_pos (a b: ℝ) : (a * b).IsPos -> (a.IsPos ↔ b.IsPos) := by
  revert a b
  suffices ∀(a b: ℝ), (a * b).IsPos -> a.IsPos -> b.IsPos by
    intro a b mpos
    apply Iff.intro
    apply this _ _ mpos
    apply this _ _ (mul_comm (α := ℝ) _ _ ▸ mpos)
  intro a b mpos apos
  have := mul_pos_of_pos_of_pos _ _ (inv_pos _ apos) mpos
  rw [←mul_assoc, inv_self_mul, one_mul] at this
  assumption

def lt_iff_mul_lt_mul_of_pos_right (a b k: ℝ) (h: 0 < k) : a < b ↔ a * k < b * k := by
  replace h : IsPos (k - 0) := h
  rw [sub_zero] at h
  show IsPos _ ↔ IsPos _
  rw [←sub_mul]
  apply Iff.intro
  intro g
  apply mul_pos_of_pos_of_pos
  assumption
  assumption
  intro g
  apply (of_mul_pos _ _ _).mpr
  exact h
  assumption

def lt_iff_mul_lt_mul_of_pos_left (a b k: ℝ) (h: 0 < k) : a < b ↔ k * a < k * b := by
  rw [mul_comm k, mul_comm k]
  apply lt_iff_mul_lt_mul_of_pos_right
  assumption

def le_iff_mul_le_mul_of_pos_right (a b k: ℝ) (h: 0 < k) : a ≤ b ↔ a * k ≤ b * k := by
  apply le_iff_of_lt_iff
  apply lt_iff_mul_lt_mul_of_pos_right
  assumption

def le_iff_mul_le_mul_of_pos_left (a b k: ℝ) (h: 0 < k) : a ≤ b ↔ k * a ≤ k * b := by
  apply le_iff_of_lt_iff
  apply lt_iff_mul_lt_mul_of_pos_left
  assumption

def div_eq_mul_inv (a b: ℝ) {h: b ≠ 0} : a /? b = a * b⁻¹? := rfl

instance : CheckedIntPow? ℝ := instCheckedIntPow

instance : IsField ℝ where
  mul_inv?_cancel := by
    intro a h
    cases a with | mk a =>
    apply Quotient.sound
    apply CauchySeq.eventually_pointwise
    have : ¬a ≈ 0 := by
      intro g
      exact h (Quotient.sound g)
    replace := CauchySeq.pos_or_neg_of_abs_pos (CauchySeq.abs_pos_of_non_zero this)
    rcases this with ⟨B, Bpos, k, h⟩ | ⟨B, Bpos, k, h⟩
    · exists k
      intro n hn
      replace h := h n hn
      dsimp at h
      unfold CauchySeq.inv
      simp
      rw [dif_neg]
      rw [mul_inv?_cancel]; rfl
      intro g
      rw [g] at h
      rw [le_iff_not_lt] at h
      contradiction
    · exists k
      intro n hn
      replace h: B ≤ -a n := h n hn
      unfold CauchySeq.inv
      simp
      rw [dif_neg]
      rw [mul_inv?_cancel]; rfl
      intro g
      rw [g] at h
      rw [le_iff_not_lt] at h
      contradiction
  div?_eq_mul_inv? := by
    intro a b h
    rfl
  zpow?_ofNat n a := rfl
  zpow?_negSucc n a _ := rfl

instance : RatCast ℝ where
  ratCast := ofRat
instance : SMul ℚ ℝ where
  smul q r := q * r

def ratCast_ne_zero (a: ℚ) (ha: a ≠ 0) : (a: ℝ) ≠ 0 := by
  intro h
  replace h := Quotient.exact h
  have ⟨k, spec⟩ := h ‖a‖ (Rat.abs_pos a ha)
  have := spec k k (le_refl _) (le_refl _)
  dsimp [CauchySeq.ofRat] at this
  rw [natCast_zero, sub_zero] at this
  exact lt_irrefl this

macro_rules
| `(tactic|invert_tactic_trivial)  => `(tactic|apply ratCast_ne_zero <;> invert_tactic_trivial)

def ofRat_div (a b: ℚ) (h: b ≠ 0) : (a: ℝ) /? (b: ℝ) = (a /? b: ℚ) := by
  apply Quotient.sound
  apply CauchySeq.pointwise
  intro n
  simp [CauchySeq.ofRat, CauchySeq.inv, Mul.mul]
  rw [dif_neg h, div?_eq_mul_inv?]

instance : IsQAlgebra ℝ where
  ratCast_eq_ratCastRec := by
    intro q
    cases q with | mk q =>
    show _ = (ofRat _) /? (ofRat _) ~(_)
    rw [ofRat_div]
    congr 1
    apply ratCast_eq_ratCastRec (Rat.mk q)

def lt_iff_div_lt_div_of_pos_right (a b k: ℝ) (h: 0 < k) : a < b ↔ a /? k < b /? k := by
  rw [div?_eq_mul_inv?, div?_eq_mul_inv?]
  apply lt_iff_mul_lt_mul_of_pos_right
  apply (lt_iff_mul_lt_mul_of_pos_right 0 k⁻¹? k _).mpr
  rw [zero_mul, inv?_mul_cancel]
  · refine ⟨1 /? 2, by decide, ?_⟩
    exists 0
    intro n h
    dsimp
    show 1 /? 2 ≤ 1
    decide
  assumption

def le_iff_div_le_div_of_pos_right (a b k: ℝ) (h: 0 < k) : a ≤ b ↔ a /? k ≤ b /? k := by
  apply le_iff_of_lt_iff
  apply lt_iff_div_lt_div_of_pos_right
  assumption

section

open Classical

def min_eq_neg_max_neg (a b: ℝ) : min a b = -max (-a) (-b) := by
  simp [min, max]
  conv => {
    rhs; rw [div_eq_mul_inv, neg_mul_left]
    simp [neg_add_rev, neg_neg, neg_sub_neg]
  }
  rw [sub_eq_add_neg, abs_sub_comm, add_comm, add_comm a b]
  rfl
def max_eq_neg_min_neg (a b: ℝ) : max a b = -min (-a) (-b) := by
  rw [min_eq_neg_max_neg, neg_neg, neg_neg, neg_neg]

def min_comm (a b: ℝ) : min a b = min b a := by
  simp [min]
  rw [add_comm, abs_sub_comm]
def max_comm (a b: ℝ) : max a b = max b a := by
  rw [max_eq_neg_min_neg, min_comm, ←max_eq_neg_min_neg]

def min_def (a b: ℝ) : min a b = if a ≤ b then a else b := by
  rw [min_comm]
  simp [min]
  rw [abs_def, le_sub_iff_add_le, zero_add]
  split
  rw [sub_eq_add_neg, neg_sub, add_comm b, sub_eq_add_neg, add_comm _ (-b),
    ←add_assoc, add_assoc a, add_neg_cancel, add_zero, ←two_mul, mul_comm,
    div_eq_mul_inv, mul_assoc, mul_inv_self, mul_one]
  rw [sub_eq_add_neg, neg_neg, sub_eq_add_neg, add_comm _ (-a), ←add_assoc,
    add_assoc b, add_neg_cancel, add_zero, ←two_mul, mul_comm,
    div_eq_mul_inv, mul_assoc, mul_inv_self, mul_one]

def max_def (a b: ℝ) : max a b = if a ≤ b then b else a := by
  rw [max_eq_neg_min_neg, min_def, neg_le_neg_iff]
  rcases lt_trichotomy a b with lt | eq | gt
  rw [if_neg, if_pos, neg_neg]
  apply le_of_lt; assumption
  rw [←lt_iff_not_le]
  assumption
  subst eq
  rw [if_pos (le_refl _), if_pos (le_refl _), neg_neg]
  rw [if_pos, if_neg, neg_neg]
  rw [←lt_iff_not_le]
  assumption
  apply le_of_lt
  assumption

end

instance : IsLinearMinMaxOrder ℝ where
  min_iff_le_left := by
    intro a b
    rw [min_def]
    apply Iff.intro
    intro h
    rw [if_pos h]
    intro h; split at h
    assumption
    rw [h]
  min_iff_le_right := by
    intro a b
    rw [min_comm, min_def]
    apply Iff.intro
    intro h
    rw [if_pos h]
    intro h; split at h
    assumption
    rw [h]
  max_iff_le_left := by
    intro a b
    rw [max_def]
    apply Iff.intro
    intro h
    rw [if_pos h]
    intro h; split at h
    assumption
    rw [h]
  max_iff_le_right := by
    intro a b
    rw [max_comm, max_def]
    apply Iff.intro
    intro h
    rw [if_pos h]
    intro h; split at h
    assumption
    rw [h]

end Real
