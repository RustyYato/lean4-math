import Math.Algebra.AddMonoidWithOne.Con
import Math.Algebra.Group.Con
import Math.Algebra.AddGroupWithOne.Defs

variable {C α: Type*} [RelLike C α] (c: C)

instance [AddGroupWithOneOps α] [IsAddGroupWithOne α] [IsAddCon C] : IsAddGroupWithOne (IsCon.Quotient c) := {
  instIsAddMonoidWithOneQuotient c, instIsAddGroupQuotient c with
  intCast_ofNat _ := by
    apply Quotient.sound
    rw [intCast_ofNat]
  intCast_negSucc _ := by
    apply Quotient.sound
    rw [intCast_negSucc]
}
