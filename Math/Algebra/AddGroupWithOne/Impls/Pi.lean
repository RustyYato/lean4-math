import Math.Algebra.AddMonoidWithOne.Impls.Pi
import Math.Algebra.Group.Impls.Pi
import Math.Algebra.AddGroupWithOne.Defs

section Pi

variable {ι: Type*} {α: ι -> Type*}

instance [∀i, AddGroupWithOneOps (α i)] [∀i, IsAddGroupWithOne (α i)] : IsAddGroupWithOne (∀i, α i) := {
  inferInstanceAs (IsAddGroup (∀i, α i)), inferInstanceAs (IsAddMonoidWithOne (∀i, α i)) with
  intCast_ofNat := fun n => by ext; apply intCast_ofNat
  intCast_negSucc := fun n => by ext; apply intCast_negSucc
}

end Pi

section Function

variable {ι: Type*} {α: Type*}

instance [AddGroupWithOneOps α] [IsAddGroupWithOne α] : IsAddGroupWithOne (ι -> α) :=
  inferInstance

end Function
