import Math.Data.Int.Basic
import Math.Data.Nat.Order

namespace int

inductive NonNeg : int -> Prop where
| intro (a: nat) : NonNeg (.ofNat a)

attribute [simp] NonNeg.intro

@[simp]
instance : LE int where
  le a b := (b - a).NonNeg
@[simp]
instance : LT int where
  lt a b := a.succ ≤ b

def NonNeg_iff_toInt_Noneg (a: int) : a.NonNeg ↔ a.toInt.NonNeg := by
  apply Iff.intro
  intro ⟨h⟩
  rw [toInt_ofNat]
  apply Int.NonNeg.mk
  intro h
  cases a using rec
  apply NonNeg.intro
  contradiction

def NonNeg.iff {a: int} : a.NonNeg ↔ ∃a', a = ofNat a' := by
  apply Iff.intro
  intro ⟨a⟩
  exists a
  intro ⟨a, h⟩
  subst h
  apply NonNeg.intro

def NonNeg_iff_ofInt_Noneg (a: Int) : (ofInt a).NonNeg ↔ a.NonNeg := by
  conv => { rhs; rw [←toInt.LeftInverse a] }
  apply flip Iff.trans
  apply NonNeg_iff_toInt_Noneg
  rfl

def LE_iff_toInt_LE (a b: int) : a ≤ b ↔ a.toInt ≤ b.toInt := by
  apply Iff.trans _ (NonNeg_iff_ofInt_Noneg _)
  show _ ↔ (b.subFast a).NonNeg
  rw [←sub_eq_subFast]
  apply Iff.refl
def LT_iff_toInt_LT (a b: int) : a < b ↔ a.toInt < b.toInt := by
  show a.succ ≤ b ↔ a.toInt + 1 ≤ b.toInt
  apply Iff.trans (LE_iff_toInt_LE _ _)
  rw [toInt_succ]

def NonNeg.succ : NonNeg a -> NonNeg a.succ := by
  intro ⟨a⟩
  apply NonNeg.intro

instance decLT (a b: int) : Decidable (a < b) := decidable_of_iff _ (LT_iff_toInt_LT a b).symm
instance decLE (a b: int) : Decidable (a ≤ b) := decidable_of_iff _ (LE_iff_toInt_LE a b).symm
instance decEQ (a b: int) : Decidable (a = b) := decidable_of_iff (a.toInt = b.toInt) (by
  apply Iff.intro
  intro h
  cases h
  rfl
  intro h
  cases h
  rfl)

instance : Min int := minOfLe
instance : Max int := maxOfLe

def le_antisymm' {a b: int} : a ≤ b -> b ≤ a -> a = b := by
  intro ab ba
  replace ⟨k₀, ab⟩  := NonNeg.iff.mp ab
  replace ⟨k₁, ba⟩ := NonNeg.iff.mp ba
  have : (b - a) + (a - b) = 0 := by
    simp [sub_eq_add_neg]
    rw [add_comm_left, add_right_comm b]
    simp
  rw [ab, ba] at this
  simp at this
  have : k₀ + k₁ = 0 := by
    apply ofNat.inj
    rw [this]
    rfl
  have ⟨_, _⟩  := nat.add_eq_zero this
  subst k₀; subst k₁
  clear this; clear this
  exact sub_eq_zero_iff.mp ba

instance : IsLinearOrder int where
  lt_iff_le_and_not_le := by
    intro a b
    apply Iff.intro
    intro h
    obtain h : (b - a.succ).NonNeg := h
    have h' := h.succ
    simp at h'
    apply And.intro
    assumption
    intro g
    obtain g : (a - b).NonNeg := g
    cases le_antisymm' h' g
    simp at h
    contradiction
    intro ⟨ab, ba⟩
    have ⟨k₀, ab⟩ := NonNeg.iff.mp ab
    apply NonNeg.iff.mpr
    exists k₀.pred
    rw [sub_succ, ab]
    cases k₀ using nat.cases
    cases sub_eq_zero_iff.mp ab
    contradiction
    rfl
  le_antisymm := le_antisymm'
  le_trans := by
    intro a b c ab bc
    replace ⟨k₀, ab⟩ := NonNeg.iff.mp ab
    replace ⟨k₁, bc⟩ := NonNeg.iff.mp bc
    apply NonNeg.iff.mpr
    exists k₀ + k₁
    rw [←add_zero (c - a), ←sub_self b, sub_eq_add_neg b, ←add_assoc,
      sub_add_assoc c, sub_eq_add_neg, add_assoc, add_comm _ (-b), ←add_assoc,
      ←sub_eq_add_neg c, bc, neg_sub, ab]
    simp [nat.add_comm]
  lt_or_le := by
    intro a b
    induction b using ind generalizing a with
    | zero =>
      cases a using rec
      right; show NonNeg _; simp
      left; show NonNeg _; simp
    | succ b ih =>
      rcases ih a.pred with ab | ba
      left; simp at ab; simp [ab]
      right; simp at ba; simp [ba]
    | pred b ih =>
      rcases ih a.succ with ab | ba
      left; simp at ab; simp [ab]
      right; simp at ba; simp [ba]
instance : IsDecidableLinearOrder int where

variable {a b: int}

section succ_pred

def succ_lt_succ_iff_lt : a.succ < b.succ ↔ a < b := by simp
def succ_le_succ_iff_le : a.succ ≤ b.succ ↔ a ≤ b := by simp
def pred_lt_pred_iff_lt : a.pred < b.pred ↔ a < b := by simp
def pred_le_pred_iff_le : a.pred ≤ b.pred ↔ a ≤ b := by simp

end succ_pred

section neg

def neg_lt_neg_iff_lt : -a < -b ↔ b < a := by simp [add_comm, sub_eq_add_neg]
def neg_le_neg_iff_le : -a ≤ -b ↔ b ≤ a := by simp [add_comm, sub_eq_add_neg]
def neg_lt_symm : -a < b ↔ -b < a := by simp [add_comm, sub_eq_add_neg]
def neg_le_symm : -a ≤ b ↔ -b ≤ a := by simp [add_comm, sub_eq_add_neg]

end neg

section add

end add

end int
