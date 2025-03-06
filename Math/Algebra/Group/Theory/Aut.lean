import Math.Algebra.Group.Theory.Basic

-- the automorphism group of a group α
instance Aut (α: Type*) [GroupOps α] [IsGroup α] : Group (α ≃* α) := by
  apply Group.ofAxiomsLeft .refl .trans .symm
  intro; rfl
  intro; apply GroupEquiv.trans_symm
  intros; rfl
