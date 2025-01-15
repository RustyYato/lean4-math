import Math.Data.Poly.Basic
import Math.Data.Set.Finite

def Poly.finite_support [Zero α] (p: Poly α) : (Set.support p.coeffs).IsFinite := by
  cases p with
  | mk p deg =>
  induction deg using Quot.ind with
  | mk deg =>
  obtain ⟨bound, le⟩ := deg
  apply Set.IsFinite.ofSubset _ (Set.mk (· ≤ bound))
  intro n h
  replace h : p n ≠ 0 := h
  show n ≤ bound
  apply Decidable.byContradiction
  intro g
  apply h
  replace g := Nat.lt_of_not_le g
  exact le _ g
