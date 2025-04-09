import Math.Algebra.Monoid.Impls.Fin
import Math.Algebra.Group.Defs

variable (n: ℕ) [NeZero n]

instance : Neg (Fin n) where
  neg x := ⟨0, x.pos⟩  - x
instance : SMul ℤ (Fin n) where
  smul := zsmulRec

instance Fin.instIsAddGroup : IsAddGroup (Fin n) where
  sub_eq_add_neg := by
    intro a b
    show Fin.mk _ _ = Fin.mk _ _
    simp
    rw [Nat.add_comm]
  zsmul_ofNat _ _ := rfl
  zsmul_negSucc _ _ := rfl
  neg_add_cancel := by
    intro a
    show Fin.mk _ _ = Fin.mk _ _
    simp
