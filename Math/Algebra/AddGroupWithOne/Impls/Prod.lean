import Math.Algebra.AddMonoidWithOne.Impls.Prod
import Math.Algebra.Group.Impls.Prod
import Math.Algebra.AddGroupWithOne.Defs

instance [AddGroupWithOneOps α] [AddGroupWithOneOps β] [IsAddGroupWithOne α] [IsAddGroupWithOne β] : IsAddGroupWithOne (α × β) := {
  inferInstanceAs (IsAddGroup (α × β)), inferInstanceAs (IsAddMonoidWithOne (α × β)) with
  intCast_ofNat := fun n => by ext <;> apply intCast_ofNat
  intCast_negSucc := fun n => by ext <;> apply intCast_negSucc
}
