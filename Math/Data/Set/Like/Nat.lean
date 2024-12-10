import Math.Data.Set.Like
import Math.Type.Finite

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

instance Nat.isSetLikeFinite {a: Nat} : IsFinite { x // x ∈ a } := IsFinite.intro a Nat.equivSetLikeFin.toEmbedding
