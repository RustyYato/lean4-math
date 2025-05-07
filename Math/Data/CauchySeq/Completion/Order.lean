import Math.Data.CauchySeq.Completion.Basic
import Math.Data.CauchySeq.Order

namespace Cauchy

variable
  [FieldOps γ] [LT γ] [LE γ] [Min γ] [Max γ]
  [IsField γ] [IsLinearLattice γ] [IsStrictOrderedSemiring γ]

open Norm.ofAbs

def Pos : Cauchy γ -> Prop := by
  apply Quotient.lift CauchySeq.Pos
  intro a b h
  ext; apply Iff.intro
  apply CauchySeq.Pos.spec
  assumption
  apply CauchySeq.Pos.spec
  apply Relation.symm; assumption

instance : LT (Cauchy γ) where
  lt := Relation.quot_rel CauchySeq.lt (· ≈ ·)

instance : LE (Cauchy γ) where
  le a b := a < b ∨ a = b

def lt_def (a b: Cauchy γ) : a < b ↔ (b - a).Pos := by
  induction a, b using ind₂
  apply Iff.rfl

instance : Relation.IsLawfulNonstrict (α := Cauchy γ) (· ≤ ·) (· < ·) (· = ·) where
  is_lawful_nonstrict _ _ := Iff.rfl

def le_iff_quot_rel (a b: Cauchy γ) : a ≤ b ↔ Relation.quot_rel CauchySeq.le (· ≈ ·) a b := by
  have := Relation.quot_rel.instIsLawfulNonstrict (α := CauchySeq γ) (rel := (CauchySeq.le (γ := γ))) (srel := CauchySeq.lt) (eqv := (· ≈ ·))
  symm; apply (this.is_lawful_nonstrict _ _)

def mk_lt (a b: CauchySeq γ) : ofSeq a < ofSeq b ↔ a < b := by rfl
def mk_le (a b: CauchySeq γ) : ofSeq a ≤ ofSeq b ↔ a ≤ b := by
  apply Iff.intro
  intro h; cases h
  left; assumption
  right; apply Quotient.exact; assumption
  intro h; cases h
  left; assumption
  right; apply Quotient.sound; assumption

def non_zero_of_Pos (a: Cauchy γ) : a.Pos -> a ≠ 0 := by
  induction a with | ofSeq a =>
  intro h
  have := CauchySeq.non_zero_of_Pos a h
  intro h; apply this; apply Quotient.exact
  assumption
def norm_pos_of_not_zero (f: Cauchy γ) (hf: f ≠ 0) : 0 < ‖f‖ := by
  induction f
  apply CauchySeq.norm_pos_of_not_zero
  intro h; apply hf
  apply Quotient.sound
  assumption

def pos_or_neg_of_abs_pos {f : Cauchy γ} (hf : Pos ‖f‖) : Pos f ∨ Pos (-f) := by
  induction f
  apply CauchySeq.pos_or_neg_of_abs_pos
  assumption
def not_neg_of_pos {f: Cauchy γ} : f.Pos -> ¬(-f).Pos := by
  induction f
  apply CauchySeq.not_neg_of_pos
def add_pos {a b: Cauchy γ} : a.Pos -> b.Pos -> (a + b).Pos := by
  induction a, b
  apply CauchySeq.add_pos
def mul_pos {a b: Cauchy γ} : a.Pos -> b.Pos -> (a * b).Pos := by
  induction a, b
  apply CauchySeq.mul_pos

def pos_or_eq_or_neg (a: Cauchy γ) : a.Pos ∨ a = 0 ∨ (-a).Pos := by
  induction a with | ofSeq a =>
  rcases (CauchySeq.pos_or_eq_or_neg a) with h | h | h
  left; assumption
  right; left; apply Quotient.sound; assumption
  right; right; assumption

@[simp]
def zero_not_pos : ¬Pos (0: Cauchy γ) := by
  intro h
  have := non_zero_of_Pos _ h
  contradiction

instance : Relation.IsStrictLinearOrder (α := Cauchy γ) (· < ·) (· = ·) :=
  inferInstanceAs (Relation.IsStrictLinearOrder (Relation.quot_rel CauchySeq.lt (· ≈ ·)) (· = ·))

instance : Relation.IsLinearOrder (α := Cauchy γ) (· ≤ ·) (· = ·) :=
  inferInstanceAs (Relation.IsLinearOrder (Relation.or_eqv (· < ·) (· = ·)) (· = ·))

instance : IsLawfulLT (Cauchy γ) :=
  have : Relation.IsLawfulStrict (α := Cauchy γ) (· ≤ ·) (· < ·) := inferInstanceAs (Relation.IsLawfulStrict (Relation.or_eqv _ _) _)
  inferInstance

instance : IsLinearOrder (Cauchy γ) := inferInstance

private def mul_le_mul_of_nonneg_left: ∀a b: Cauchy γ, a ≤ b -> ∀c, 0 ≤ c -> c * a ≤ c * b := by
  intro a b ab c hc
  rcases Or.symm hc with rfl | hc
  simp
  rcases Or.symm ab with rfl | ab
  rfl
  left
  rw [lt_def]
  show (c * b - c * a).Pos
  rw [←mul_sub]
  apply mul_pos
  rw [lt_def] at hc
  rwa [←sub_zero c]
  rwa [lt_def] at ab

instance : IsStrictOrderedSemiring (Cauchy γ) where
  add_le_add_left := by
    intro a b ab c
    rcases Or.symm ab with rfl | h
    · rfl
    · induction a, b, c with | ofSeq a b c =>
      obtain ⟨B, Bpos, i, h⟩ := h
      left; refine ⟨B, Bpos, i, ?_⟩
      intro n hn
      replace h : B ≤ _ := h n hn
      rwa [sub_add, add_sub_assoc, add_comm, add_sub_assoc,
        sub_self, add_zero]
  mul_nonneg a b ha hb := by
    rcases Or.symm ha with rfl | ha
    rw [zero_mul]
    rcases Or.symm hb with rfl | hb
    rw [mul_zero]
    left; rw [lt_def]; show (a * _ - 0).Pos
    rw [lt_def] at ha hb
    simp; apply mul_pos
    rwa [←sub_zero a]
    rwa [←sub_zero b]
  mul_le_mul_of_nonneg_left := by apply mul_le_mul_of_nonneg_left
  mul_le_mul_of_nonneg_right := by
    intro a b h c
    rw [mul_comm _ c, mul_comm _ c]
    apply mul_le_mul_of_nonneg_left
    assumption
  zero_le_one := by
    left
    exists 1
    apply And.intro
    apply zero_lt_one
    exists 0
    intro n hn
    show 1 ≤ (1 - 0: γ)
    simp
  mul_pos := by
    intro a b ha hb
    rw [lt_def] at *
    replace ha : (a - 0).Pos := ha
    replace hb : (b - 0).Pos := hb
    show (a * b - 0).Pos
    simp at ha hb
    simp [mul_pos ha hb]

variable [DecidableEq γ]

instance : Min (Cauchy γ) where
  min x y := (x + y - ‖x - y‖) /? 2
instance : Max (Cauchy γ) where
  max x y := (x + y + ‖x - y‖) /? 2

private def max_comm (a b: Cauchy γ) : max a b = max b a := by
  simp [Max.max]
  congr 1
  induction a, b with | ofSeq a b =>
  apply Quotient.sound
  apply CauchySeq.pointwise
  intro i
  show a i + b i + ‖a i - b i‖ = b i + a i + ‖b i - a i‖
  rw [norm_sub_comm, add_comm (a i)]
private def min_comm (a b: Cauchy γ) : min a b = min b a := by
  simp [Min.min]
  congr 1
  induction a, b with | ofSeq a b =>
  apply Quotient.sound
  apply CauchySeq.pointwise
  intro i
  show a i + b i - ‖a i - b i‖ = b i + a i - ‖b i - a i‖
  rw [norm_sub_comm, add_comm (a i)]

open Classical in
private noncomputable instance : DecidableLE (Cauchy γ) := inferInstance

private def norm_def (a: Cauchy γ) : ‖a‖ = if 0 ≤ a then a else -a := by
  rcases lt_trichotomy 0 a with ha | rfl | ha
  · induction a with | ofSeq a =>
    rw [if_pos (le_of_lt ha)]
    obtain ⟨B, Bpos, i, h⟩ := ha
    apply Quotient.sound
    apply CauchySeq.eventually_pointwise
    exists i
    intro n hn
    have : B ≤ a n - 0 := h n hn
    simp at this
    apply abs_of_nonneg
    apply le_trans; apply le_of_lt
    assumption
    assumption
  · rw [if_pos (le_refl _)]
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro i
    apply abs_zero
  · induction a with | ofSeq a =>
    rw [if_neg (not_le_of_lt ha)]
    obtain ⟨B, Bpos, i, h⟩ := ha
    apply Quotient.sound
    apply CauchySeq.eventually_pointwise
    exists i
    intro n hn
    have : B ≤ 0 - a n := h n hn
    simp [zero_sub] at this
    show |a n| = - a n
    rw [←abs_neg]
    apply abs_of_nonneg
    apply le_trans; apply le_of_lt
    assumption
    assumption

def min_def (a b: Cauchy γ) : min a b = if a ≤ b then a else b := by
  rw [min_comm]
  simp [min]
  rw [norm_def]
  classical
  split <;> rename_i h
  rw [le_sub_iff_add_le, zero_add] at h; rw [if_pos h]
  rw [sub_eq_add_neg, neg_sub, add_comm b, sub_eq_add_neg, add_comm _ (-b),
    ←add_assoc, add_assoc a, add_neg_cancel, add_zero, ←two_mul, mul_comm,
    div?_eq_mul_inv?, mul_assoc, mul_inv?_cancel, mul_one]
  rw [le_sub_iff_add_le, zero_add] at h; rw [if_neg h]
  rw [sub_eq_add_neg, neg_neg, sub_eq_add_neg, add_comm _ (-a), ←add_assoc,
    add_assoc b, add_neg_cancel, add_zero, ←two_mul, mul_comm,
    div?_eq_mul_inv?, mul_assoc, mul_inv?_cancel, mul_one]

def max_def (a b: Cauchy γ) : max a b = if a ≤ b then b else a := by
  rw [max_comm]
  simp [max]
  rw [norm_def]
  classical
  split <;> rename_i h
  rw [le_sub_iff_add_le, zero_add] at h; rw [if_pos h]
  rw [sub_eq_add_neg, add_assoc, add_left_comm a, ←add_assoc,
    add_neg_cancel, add_zero, ←mul_two, div?_eq_mul_inv?,
    mul_assoc, mul_inv?_cancel, mul_one]
  rw [le_sub_iff_add_le, zero_add] at h; rw [if_neg h]
  rw [neg_sub, add_comm b, sub_eq_add_neg, add_assoc, add_left_comm b,
    ←add_assoc, add_neg_cancel, add_zero, ←mul_two, div?_eq_mul_inv?,
    mul_assoc, mul_inv?_cancel, mul_one]

private def le_max_left (a b: Cauchy γ) : a ≤ a ⊔ b := by
  rw [max_def]
  split
  assumption
  rfl
private def min_le_left (a b: Cauchy γ) : a ⊓ b ≤ a := by
  rw [min_def]
  split
  rfl
  apply le_of_not_le
  assumption

instance : IsLattice (Cauchy γ) where
  le_max_left := le_max_left
  le_max_right a b := max_comm a b ▸ le_max_left b a
  max_le := by
    intro a b k ak kb
    rw [max_def]
    split
    assumption
    assumption
  min_le_left := min_le_left
  min_le_right a b := min_comm a b ▸ min_le_left b a
  le_min := by
    intro a b k ka kb
    rw [min_def]
    split
    assumption
    assumption

instance : IsLinearLattice (Cauchy γ) where

end Cauchy

namespace CauchySeq

variable
  [FieldOps γ] [LT γ] [LE γ] [Min γ] [Max γ]
  [IsField γ] [IsLinearLattice γ] [IsStrictOrderedSemiring γ]

open Norm.ofAbs

def le_eventually_pointwise (a b: CauchySeq γ) :
  (Eventually fun n => a n ≤ b n) ->
  a ≤ b := by
  intro h
  rw [←Cauchy.mk_le, le_iff_not_lt]
  intro ⟨B, B_pos, spec⟩
  replace spec := h.merge spec; clear h
  obtain ⟨k, spec⟩ := spec
  replace spec := spec k (le_refl _)
  obtain ⟨h, spec⟩ := spec
  replace spec: 0 < a _ - b _ := lt_of_lt_of_le B_pos spec
  replace spec := add_lt_add_of_lt_of_le _ _ _ _ spec (le_refl (b k))
  rw [zero_add, sub_eq_add_neg, add_assoc, neg_add_cancel,
    add_zero] at spec
  exact not_le_of_lt spec h

def le_pointwise (a b: CauchySeq γ) :
  (∀n, a n ≤ b n) ->
  a ≤ b := by
  intro h
  apply le_eventually_pointwise
  exists 0
  intro n g
  apply h

end CauchySeq
