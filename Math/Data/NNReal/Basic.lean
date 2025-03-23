import Math.Data.Real.OrderedAlgebra
import Math.Order.OrderIso.Linear

def NNReal := { x: ℝ // 0 ≤ x }

notation "ℝ≥0" => NNReal

namespace NNReal

instance : Add ℝ≥0 where
  add := fun ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a + b, Real.add_nonneg ha hb⟩
instance : Mul ℝ≥0 where
  mul := fun ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a * b, Real.mul_nonneg ha hb⟩
instance : Zero ℝ≥0 where
  zero := ⟨0, le_refl _⟩
instance : One ℝ≥0 where
  one := ⟨1, zero_le_one⟩
instance : NatCast ℝ≥0 where
  natCast n := ⟨n, by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [natCast_add]
      apply Real.add_nonneg
      assumption
      exact zero_le_one⟩
instance : OfNat ℝ≥0 n where
  ofNat := n
instance : CheckedInv? ℝ≥0 where
  checked_invert a h := ⟨a.val⁻¹? ~(by
    intro g; apply h
    cases a; congr), by
    apply le_of_lt
    apply inv?_pos
    apply lt_of_le_of_ne
    apply a.property
    symm; intro g; apply h
    cases a; congr⟩
instance : CheckedDiv? ℝ≥0 where
  checked_div a b h := a * b⁻¹?
instance : SMul ℕ ℝ≥0 where
  smul n a := n * a
instance : Pow ℝ≥0 ℕ where
  pow a n := ⟨a.val ^ n, by
    induction n with
    | zero =>
      rw [npow_zero]
      apply zero_le_one
    | succ n ih =>
      rw [npow_succ]
      apply Real.mul_nonneg
      assumption
      exact a.property⟩
instance : CheckedIntPow? ℝ≥0 := instCheckedIntPow

def embedReal : ℝ≥0 ↪+* ℝ where
  toFun x := x.val
  inj' := Subtype.val_inj
  resp_zero := rfl
  resp_one := rfl
  resp_add := rfl
  resp_mul := rfl

instance : IsSemifield ℝ≥0 where
  exists_ne := by
    refine ⟨0, 1, ?_⟩
    intro h
    rw [←embedReal.inj.eq_iff] at h
    apply zero_ne_one _ h
  add_comm _ _ := by
    apply embedReal.inj
    apply add_comm
  add_assoc _ _ _ := by
    apply embedReal.inj
    apply add_assoc
  zero_add _ := by
    apply embedReal.inj
    apply zero_add
  add_zero _ := by
    apply embedReal.inj
    apply add_zero
  natCast_zero := by
    apply embedReal.inj
    apply natCast_zero
  natCast_succ _ := by
    apply embedReal.inj
    apply natCast_succ
  ofNat_eq_natCast _ := by
    apply embedReal.inj
    apply ofNat_eq_natCast
  mul_comm _ _ := by
    apply embedReal.inj
    apply mul_comm
  mul_assoc _ _ _ := by
    apply embedReal.inj
    apply mul_assoc
  zero_nsmul _ := by
    apply embedReal.inj
    apply zero_nsmul
  succ_nsmul _ _ := by
    apply embedReal.inj
    apply succ_nsmul
  npow_zero _ := by
    apply embedReal.inj
    apply npow_zero
  npow_succ _ _ := by
    apply embedReal.inj
    apply npow_succ
  zero_mul _ := by
    apply embedReal.inj
    apply zero_mul
  mul_zero _ := by
    apply embedReal.inj
    apply mul_zero
  one_mul _ := by
    apply embedReal.inj
    apply one_mul
  mul_one _ := by
    apply embedReal.inj
    apply mul_one
  left_distrib _ _ _ := by
    apply embedReal.inj
    apply mul_add
  right_distrib _ _ _ := by
    apply embedReal.inj
    apply add_mul
  mul_inv?_cancel _ _ := by
    apply embedReal.inj
    apply mul_inv?_cancel
  div?_eq_mul_inv? _ _ _ := rfl
  zpow?_ofNat _ _ := rfl
  zpow?_negSucc _ _ _ := rfl

instance : LE ℝ≥0 where
  le a b := a.val ≤ b.val

instance : LT ℝ≥0 where
  lt a b := a.val < b.val

instance : Bot ℝ≥0 where
  bot := 0

instance : IsLawfulBot ℝ≥0 where
  bot_le x := x.property

def orderEmbedReal : ℝ≥0 ↪o ℝ where
  toEmbedding := Embedding.subtypeVal
  resp_rel := Iff.rfl

instance : Min ℝ≥0 where
  min a b := ⟨min a.val b.val, by
    apply le_min_iff.mpr
    apply And.intro
    exact a.property
    exact b.property⟩

instance : Max ℝ≥0 where
  max a b := ⟨max a.val b.val, by
    apply le_max_iff.mpr
    left; exact a.property⟩

instance : IsLawfulLT ℝ≥0 where
  lt_iff_le_and_not_le {a b} := by apply lt_iff_le_and_not_le (α := ℝ)

instance : IsLinearOrder ℝ≥0 := orderEmbedReal.inducedIsLinearOrder
instance : IsLinearMinMaxOrder ℝ≥0 where
  min_iff_le_left {a b} := by
    rw [←orderEmbedReal.inj.eq_iff]
    apply min_iff_le_left (α := ℝ)
  min_iff_le_right {a b} := by
    rw [←orderEmbedReal.inj.eq_iff]
    apply min_iff_le_right (α := ℝ)
  max_iff_le_left {a b} := by
    rw [←orderEmbedReal.inj.eq_iff]
    apply max_iff_le_left (α := ℝ)
  max_iff_le_right {a b} := by
    rw [←orderEmbedReal.inj.eq_iff]
    apply max_iff_le_right (α := ℝ)

instance : NeZero (2: ℝ) where
  out := by
    intro h
    have ⟨k, spec⟩ := Quotient.exact h (1 /? 2) (by decide)
    replace spec := spec _ _ (le_refl _) (le_refl _)
    contradiction

instance : IsStrictOrderedSemiring ℝ≥0 where
  add_le_add_left := sorry
  le_iff_nsmul_le := sorry
  mul_nonneg := sorry

end NNReal
