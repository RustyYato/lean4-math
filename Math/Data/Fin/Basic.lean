import Math.Function.Basic
import Math.Algebra.Ring.Defs
import Math.Algebra.Semiring.Order.Defs
import Math.Data.Fin.Pairing

def Fin.castLE_ne_addNat (x: Fin n) (y: Fin m) : x.castLE (Nat.le_add_left _ _) ≠ y.addNat n := by
  intro h
  cases x with | mk x xLt =>
  cases y with | mk y yLt =>
  unfold Fin.castLE Fin.addNat at h
  dsimp at h
  have := Fin.mk.inj h
  subst x
  exact Nat.not_lt_of_le (Nat.le_add_left _ _) xLt

def Fin.addNat_inj : Function.Injective (Fin.addNat · k (n := n)) := by
  intro ⟨x, _⟩ ⟨y, _⟩ eq
  replace eq := Fin.val_inj.mpr eq
  dsimp at eq
  congr
  exact Nat.add_right_cancel eq
