import Math.Data.Set.Like
import Math.Type.Finite
import Math.Order.Lattice.SetLike
import Math.Data.Nat.Lattice

instance : SetLike Nat Nat where
  coe lim := Set.mk fun x => x < lim
  coe_inj a b := by
    dsimp
    intro h
    replace h := fun x => Eq.to_iff (congrFun (Set.mk.inj h) x)
    apply Nat.le_antisymm
    · cases a with
      | zero => apply Nat.zero_le
      | succ a =>
        apply Nat.succ_le_of_lt
        apply (h a).mp
        apply Nat.lt_succ_self
    · cases b with
      | zero => apply Nat.zero_le
      | succ b =>
        apply Nat.succ_le_of_lt
        apply (h b).mpr
        apply Nat.lt_succ_self

def Nat.equivSetLikeFin : { x // x ∈ a } ≃ Fin a where
  toFun | ⟨x, lt⟩ => ⟨x, lt⟩
  invFun | ⟨x, lt⟩ => ⟨x, lt⟩
  leftInv _ := rfl
  rightInv _ := rfl

instance Nat.isSetLikeFinite {a: Nat} : IsFinite { x // x ∈ a } := IsFinite.intro a Nat.equivSetLikeFin

instance (a b: Nat) : Decidable (a ∈ b) := inferInstanceAs (Decidable (a < b))

instance : IsSetLikeLattice Nat where
  min_eq_set_min a b := by
    ext x
    exact Nat.lt_min
  max_eq_set_max a b := by
    ext x
    show x < max a b ↔ x < a ∨ x < b
    exact lt_max_iff
  le_iff_sub a b := by
    apply Iff.intro
    intro h x hx
    exact Nat.lt_of_lt_of_le hx h
    intro h
    cases a
    apply Nat.zero_le
    rename_i a
    apply Nat.succ_le_of_lt
    apply h
    apply Nat.lt_succ_self

instance : IsLawfulEmptySetLike Nat where
  elim x := Nat.not_lt_zero _ x.property
