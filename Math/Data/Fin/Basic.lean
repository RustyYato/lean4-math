import Math.Function.Basic
import Math.Logic.Equiv.Basic
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

def Fin.isoPair : Fin n × Fin m ≃ Fin (n * m) where
  toFun x := Fin.pair x.1 x.2
  invFun x := ⟨x.pair_left, x.pair_right⟩
  leftInv := by
    intro x
    simp
    rw [pair_pair_left, pair_pair_right]
  rightInv := by
    intro x
    simp
    rw [pair_split_eq_self]

def Fin.equivAdd (n m: Nat) : Fin n ⊕ Fin m ≃ Fin (n + m) where
  toFun
  | .inl x => x.addNat m
  | .inr x => x.castLE (Nat.le_add_left _ _)
  invFun x :=
    if h:x.val < m then .inr ⟨x, h⟩ else .inl ⟨x.val - m, by
      apply Nat.sub_lt_left_of_lt_add
      apply Nat.le_of_not_lt
      assumption
      cases x; dsimp
      rw [Nat.add_comm]; assumption⟩
  leftInv x := by
    dsimp
    cases x <;> rename_i x <;> dsimp
    rw [dif_neg]
    congr
    rw [Nat.add_sub_cancel]
    apply Nat.not_lt_of_le
    apply Nat.le_add_left
    rw [dif_pos]
    exact x.isLt
  rightInv x := by
    dsimp
    by_cases h:x.val < m
    rw [dif_pos h]
    rfl
    rw [dif_neg h]
    dsimp; congr
    rw [Nat.sub_add_cancel]
    apply Nat.le_of_not_lt
    assumption

def Fin.equivMul (n m: Nat) : Fin n × Fin m ≃ Fin (n * m) where
  toFun | ⟨x, y⟩ => Fin.pair x y
  invFun x := ⟨x.pair_left, x.pair_right⟩
  leftInv x := by
    dsimp
    rw [Fin.pair_pair_left]
    rw [Fin.pair_pair_right]
  rightInv x := by
    dsimp
    rw [Fin.pair_split_eq_self]

def Fin.addNat_inj : Function.Injective (Fin.addNat · k (n := n)) := by
  intro ⟨x, _⟩ ⟨y, _⟩ eq
  replace eq := Fin.val_inj.mpr eq
  dsimp at eq
  congr
  exact Nat.add_right_cancel eq
