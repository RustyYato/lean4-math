import Math.Algebra.AddMonoidWithOne.Impls.Fin
import Math.Algebra.Group.Impls.Fin
import Math.Algebra.AddGroupWithOne.Defs

variable (n: ℕ) [NeZero n]

instance : IntCast (Fin n) where
  intCast m := ⟨(m % n).toNat, by
    have := NeZero.ne n
    apply Int.ofNat_lt.mp
    rw [Int.toNat_of_nonneg]
    refine Int.emod_lt_of_pos m ?_
    omega
    refine Int.emod_nonneg m ?_
    omega⟩

instance Fin.instIsAddGroupWithOne : IsAddGroupWithOne (Fin n) := {
  Fin.instIsAddMonoidWithOne n, Fin.instIsAddGroup n with
  intCast_ofNat _ := rfl
  intCast_negSucc _ := by
    have := NeZero.ne n
    apply neg_inj.mp
    rw [neg_neg]
    show Fin.mk _ _ = Fin.mk _ _
    congr 1
    rw [Int.negSucc_emod]
    simp
    rw [Int.sub_sub]
    apply Int.ofNat_inj.mp
    simp
    rw [Int.ofNat_sub]
    simp
    rw [Int.max_eq_left]
    rw [Int.sub_sub_self]
    rw [Int.add_emod, Int.emod_emod, ←Int.add_emod, Int.add_comm]
    apply Int.le_sub_left_of_add_le
    simp; rw [Int.add_comm]
    apply Int.add_one_le_iff.mpr
    apply Int.emod_lt_of_pos
    omega
    omega
    omega
}
