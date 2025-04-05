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

end Cauchy
