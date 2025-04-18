import Math.Algebra.Module.SetLike.Group
import Math.Algebra.Module.SetLike.Basic
import Math.Algebra.Module.Con
import Math.Algebra.Group.Action.Basic
import Math.Algebra.Group.Con
import Math.Algebra.Ring.Defs

namespace Submodule

variable
  [RingOps R] [IsRing R]
  [AddGroupOps M] [IsAddGroup M] [IsAddCommMagma M]
  [SMul R M] [IsModule R M]

def toCon (s: Submodule R M) : LinearCon R M where
  r a b := a - b ∈ s
  iseqv := {
    refl m := by rw [sub_self]; apply mem_zero
    symm {x y} h := by
      rw [←neg_sub]; apply mem_neg
      assumption
    trans {x y z} h g := by
      rw [←add_zero x, ←neg_add_cancel y, ←add_assoc,
        ←sub_eq_add_neg, add_sub_assoc]
      apply mem_add
      assumption
      assumption
  }
  resp_add {a b c d} h g := by
    rw [sub_add, add_sub_assoc, sub_eq_add_neg _ c, add_comm_right _ _ (-c),
      ←sub_eq_add_neg]
    apply mem_add
    assumption
    assumption
  resp_smul r a b h := by
    rw [←smul_sub]
    apply mem_smul
    assumption

def ofCon (c: LinearCon R M) : Submodule R M where
  carrier := Set.mk (c 0)
  mem_zero := by show c 0 0; rfl
  mem_add {a b} ha hb := by
    show c 0 _
    rw [←add_zero 0]
    apply resp_add
    assumption
    assumption
  mem_smul' r a h := by
    show c 0 (r • a)
    rw [←smul_zero r]
    apply resp_smul
    assumption

def equivCon : Submodule R M ≃ LinearCon R M where
  toFun := toCon
  invFun := ofCon
  leftInv s := by
    ext x
    show _ - _ ∈ s ↔ _
    rw [zero_sub]
    apply Iff.intro
    intro h; rw [←neg_neg x]; apply mem_neg; assumption
    apply mem_neg
  rightInv c := by
    apply le_antisymm
    intro x y
    show c _ _ -> c _ _
    intro h
    have : c (0 + y) (x - y + y) := by
      apply resp_add
      assumption; rfl
    simp [sub_add_cancel] at this
    apply Relation.symm; assumption
    intro x y h
    show c 0 _
    rw [←sub_self y]
    apply resp_sub
    apply Relation.symm; assumption
    rfl

end Submodule
