import Math.Order.Linear

def Fin.lt_or_eq_of_le {a b: Fin n} : a ≤ b -> a < b ∨ a = b := by
  intro h
  cases Nat.lt_or_eq_of_le (Fin.le_def.mp h)
  left; apply Fin.lt_def.mpr; assumption
  right; rename_i h; rw [Fin.val_inj.mp h]

instance : IsLinearOrder (Fin n) where
  lt_iff_le_and_not_le := by
    intro a b
    apply Iff.intro
    intro h
    apply And.intro
    apply Fin.le_of_lt; assumption
    intro h
    rcases Fin.lt_or_eq_of_le h with h | eq
    have := Fin.lt_asymm h
    contradiction
    subst b
    have := Fin.lt_irrefl a
    contradiction
    intro ⟨h, g⟩
    rcases Fin.lt_or_eq_of_le h with h | eq
    assumption
    subst b
    contradiction
  le_antisymm := Fin.le_antisymm
  lt_or_le a b := by
    rcases Fin.le_total a b with ab | ba
    rcases Fin.lt_or_eq_of_le ab with ab | eq
    left; apply Fin.lt_def.mpr; assumption
    right; rw [eq]; apply Fin.le_refl
    right; assumption
  le_trans := Fin.le_trans

local instance : Min (Fin n) := minOfLe
local instance : Max (Fin n) := maxOfLe

instance : IsDecidableLinearOrder (Fin n) where
