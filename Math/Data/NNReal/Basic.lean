import Math.Data.Real.OrderedAlgebra
import Math.Order.OrderIso
import Math.Algebra.Semifield.SetLike.Basic

abbrev Real.nonneg : Subsemifield ℝ where
  carrier := Set.mk (0 ≤ ·)
  mem_zero := by apply le_refl (0: ℝ)
  mem_one := by apply zero_le_one (α := ℝ)
  mem_add := by
    intro a b ha hb
    apply Real.add_nonneg
    assumption
    assumption
  mem_mul := by
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
  map_zero := rfl
  map_one := rfl
  map_add := rfl
  map_mul := rfl

def ofReal (r: ℝ) : ℝ≥0 where
  val := max r 0
  property := by apply le_max_right (α := ℝ)

def ofReal_embedReal (r: ℝ) (h: 0 ≤ r) : embedReal (ofReal r) = r := by
  show max r 0 = r
  rwa [max_eq_left.mpr]

def embedReal_ofReal (r: ℝ≥0) : ofReal (embedReal r) = r := by
  unfold ofReal
  congr
  rw [max_eq_left.mpr]
  rfl
  exact r.property

def isNonneg (x: ℝ≥0) : 0 ≤ x.val := x.property

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
instance : IsLinearLattice ℝ≥0 := sorry -- FIXME
  -- min_iff_le_left {a b} := by
  --   rw [←orderEmbedReal.inj.eq_iff]
  --   apply min_iff_le_left (α := ℝ)
  -- min_iff_le_right {a b} := by
  --   rw [←orderEmbedReal.inj.eq_iff]
  --   apply min_iff_le_right (α := ℝ)
  -- max_iff_le_left {a b} := by
  --   rw [←orderEmbedReal.inj.eq_iff]
  --   apply max_iff_le_left (α := ℝ)
  -- max_iff_le_right {a b} := by
  --   rw [←orderEmbedReal.inj.eq_iff]
  --   apply max_iff_le_right (α := ℝ)

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

instance : HasChar ℝ≥0 0 :=
  HasChar.eq_zero_of_add_hom embedReal

instance : IsAddCancel ℝ≥0 where
  add_left_cancel := by
    intro a b k h
    have : -embedReal k + embedReal (k + a) = -embedReal k + embedReal (k + b) := by rw [h]
    apply embedReal.inj
    simpa [map_add, ←add_assoc, neg_add_cancel] using this
  add_right_cancel := by
    intro a b k h
    have : embedReal (a + k) + -embedReal k = embedReal (b + k) + -embedReal k := by rw [h]
    apply embedReal.inj
    simpa [map_add, add_assoc, neg_add_cancel] using this

def of_add_eq_zero (a b: ℝ≥0) : a + b = 0 -> a = 0 ∧ b = 0 := by
  intro h
  rcases lt_or_eq_of_le (bot_le a) with ha | ha
  have : 0 < a + b := by
    rw [←add_zero 0]
    apply add_lt_add_of_lt_of_le
    assumption
    apply bot_le
  rw [h] at this
  have := lt_irrefl this
  contradiction
  rcases lt_or_eq_of_le (bot_le b) with hb | hb
  have : 0 < a + b := by
    rw [←add_zero 0]
    apply add_lt_add_of_le_of_lt
    apply bot_le
    assumption
  rw [h] at this
  have := lt_irrefl this
  contradiction
  apply And.intro <;> (symm; assumption)

instance : NeZero (2: ℝ≥0) where
  out := by
    intro h
    have : embedReal 2 = embedReal 0 := by rw [h]
    exact NeZero.ne (n := 2) (R := ℝ) this

def ofReal_injOn : Function.InjectiveOn ofReal (Set.Ici 0) := by
  intro x y hx hy h
  have := Subtype.mk.inj h
  rwa [max_eq_left.mpr, max_eq_left.mpr] at this
  assumption
  assumption

def ofReal_lt (h: 0 ≤ a) (g: a < b) : ofReal a < ofReal b := by
  apply (lt_max_iff (α := ℝ)).mpr
  simp [ofReal]
  left
  apply max_lt_iff.mpr
  apply And.intro
  assumption
  apply lt_of_le_of_lt
  assumption
  assumption

def of_ofReal_lt (h: ofReal a < ofReal b) : a < b := by
  replace h := (lt_max_iff (α := ℝ)).mp h
  rcases h with h | h
  exact (max_lt_iff.mp h).left
  have := lt_irrefl (max_lt_iff.mp h).right
  contradiction

def ofReal_add (x y: ℝ) (hx: 0 ≤ x) (hy: 0 ≤ y) : ofReal (x + y) = ofReal x + ofReal y := by
  unfold ofReal
  congr; simp
  iterate 3 rw [max_eq_left.mpr]
  assumption
  assumption
  apply Real.add_nonneg
  assumption
  assumption

def ofReal_mul (x y: ℝ) (hx: 0 ≤ x) (hy: 0 ≤ y) : ofReal (x * y) = ofReal x * ofReal y := by
  unfold ofReal
  congr; simp
  iterate 3 rw [max_eq_left.mpr]
  assumption
  assumption
  apply Real.mul_nonneg
  assumption
  assumption

end NNReal
