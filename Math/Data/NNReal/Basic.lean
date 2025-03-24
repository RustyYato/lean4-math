import Math.Data.Real.OrderedAlgebra
import Math.Order.OrderIso
import Math.Algebra.Semifield.SetLike.Basic

abbrev Real.nonneg : Subsemifield ℝ where
  carrier := Set.mk (0 ≤ ·)
  mem_zero' := by apply le_refl (0: ℝ)
  mem_one' := by apply zero_le_one (α := ℝ)
  mem_add' := by
    intro a b ha hb
    apply Real.add_nonneg
    assumption
    assumption
  mem_mul' := by
    intro a b ha hb
    apply Real.mul_nonneg
    assumption
    assumption
  mem_inv?' := by
    intro a h ha
    cases lt_or_eq_of_le (α := ℝ) ha
    apply le_of_lt (α := ℝ)
    apply inv?_pos
    assumption
    subst a
    contradiction

def Real.mem_nonneg (x: ℝ) : x ∈ Real.nonneg ↔ 0 ≤ x := Iff.rfl

def NNReal : Type := Real.nonneg

instance : SemifieldOps NNReal := inferInstanceAs (SemifieldOps Real.nonneg)
instance : IsSemifield NNReal := inferInstanceAs (IsSemifield Real.nonneg)

notation "ℝ≥0" => NNReal

namespace NNReal

def embedReal : ℝ≥0 ↪+* ℝ where
  toFun x := x.val
  inj' := Subtype.val_inj
  resp_zero := rfl
  resp_one := rfl
  resp_add := rfl
  resp_mul := rfl

instance : LE ℝ≥0 := inferInstanceAs (LE (Subtype _))
instance : LT ℝ≥0 := inferInstanceAs (LT (Subtype _))

instance : Bot ℝ≥0 where
  bot := 0

instance : IsLawfulBot ℝ≥0 where
  bot_le x := x.property

def orderEmbedReal : ℝ≥0 ↪o ℝ where
  toEmbedding := Embedding.subtypeVal
  resp_rel := Iff.rfl

instance : Min ℝ≥0 where
  min a b := ⟨min a.val b.val, by
    rw [Real.mem_nonneg]
    apply le_min_iff.mpr
    apply And.intro
    exact a.property
    exact b.property⟩

instance : Max ℝ≥0 where
  max a b := ⟨max a.val b.val, by
    rw [Real.mem_nonneg]
    apply le_max_iff.mpr
    left; exact a.property⟩

instance : IsLinearOrder ℝ≥0 := inferInstanceAs (IsLinearOrder (Subtype _))
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
  zero_le_one := by apply bot_le
  add_le_add_left := by
    intro a b h c
    apply add_le_add_left (α := ℝ)
    assumption
  mul_nonneg := by
    intro a b
    apply mul_nonneg (α := ℝ)
  mul_pos := by
    intro a b
    apply mul_pos (α := ℝ)
  mul_le_mul_of_nonneg_left := by
    intro a b h c
    apply mul_le_mul_of_nonneg_left (α := ℝ)
    assumption
  mul_le_mul_of_nonneg_right := by
    intro a b h c
    apply mul_le_mul_of_nonneg_right (α := ℝ)
    assumption

instance : IsOrderedCommMonoid ℝ≥0 where
  mul_le_mul_left := by
    intro a b h c
    apply mul_le_mul_of_nonneg_left
    assumption
    apply bot_le

end NNReal
