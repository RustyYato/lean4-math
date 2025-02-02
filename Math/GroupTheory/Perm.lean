import Math.GroupTheory.Subgroup

namespace Group

def PermType (α: Type*) := α ≃ α

instance : One (PermType α) where
  one := .refl

instance : Mul (PermType α) where
  mul := .trans

instance : Inv (PermType α) where
  inv := .symm

def Perm (α: Type*) : Group (PermType α) := by
  apply Group.ofAxiomsLeft
  intro
  rfl
  intro x
  apply Equiv.symm_trans_self
  intro  _ _ _; rfl

end Group
