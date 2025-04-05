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
  lt a b := (b - a).Pos

instance : LE (Cauchy γ) where
  le a b := a < b ∨ a = b

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
  by_cases h:a = 0
  right; left; assumption
  cases pos_or_neg_of_abs_pos (f := a) (by
    have : (‖a‖ - 0).Pos := (norm_pos_of_not_zero _ h)
    rwa [sub_zero] at this)
  left; assumption
  right; right; assumption

@[simp]
def zero_not_pos : ¬Pos (0: Cauchy γ) := by
  intro h
  have := non_zero_of_Pos _ h
  contradiction

private def lt_asymm {a b: Cauchy γ} : a < b -> b < a -> False := by
  intro h g
  replace h : (b - a).Pos := h
  replace g : (a - b).Pos := g
  rw [←neg_sub] at g
  have := not_neg_of_pos h
  contradiction

instance : IsLinearOrder (Cauchy γ) where
  lt_iff_le_and_not_le := by
    intro a b
    apply Iff.intro
    intro h
    apply And.intro
    left; assumption
    intro g
    rcases g  with g | g
    have := lt_asymm h g
    contradiction
    subst g
    replace h : (b - b).Pos := h
    simp at h
    intro ⟨h, g⟩
    apply h.resolve_right
    rintro rfl
    apply g
    right; rfl
  le_antisymm := by
    intro a b h g
    cases h <;> cases g <;> rename_i h g
    have := lt_asymm h g
    contradiction
    symm; repeat assumption
  le_trans := by
    suffices ∀{a b c: Cauchy γ}, (b - a).Pos -> (c - b).Pos -> (c - a).Pos by
      intro a b c ab bc
      rcases ab with ab | rfl <;> rcases bc with bc | rfl
      · left; apply this <;> assumption
      · left; assumption
      · left; assumption
      · right; rfl
    intro a b c ab bc
    have ac := add_pos bc ab
    rwa [←add_sub_assoc, sub_add_cancel] at ac
  lt_or_le := by
    intro a b
    rcases pos_or_eq_or_neg (b - a) with h | h | h
    left; assumption
    right; right; apply eq_of_sub_eq_zero; assumption
    right; left
    show (a - b).Pos
    rwa [←neg_sub]

private def mul_le_mul_of_nonneg_left: ∀a b: Cauchy γ, a ≤ b -> ∀c, 0 ≤ c -> c * a ≤ c * b := by
  intro a b ab c hc
  rcases Or.symm hc with rfl | hc
  simp
  rcases Or.symm ab with rfl | ab
  rfl
  left
  show (c * b - c * a).Pos
  rw [←mul_sub]
  apply mul_pos
  rwa [←sub_zero c]
  assumption

instance : IsOrderedSemiring (Cauchy γ) where
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
    left; show (a * _ - 0).Pos
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

-- set_option trace.Meta.synthInstance true

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

instance : IsLinearLattice (Cauchy γ) := {
  inferInstanceAs (IsPartialOrder (Cauchy γ)),
  inferInstanceAs (IsLinearOrder (Cauchy γ)) with
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
}

end Cauchy
