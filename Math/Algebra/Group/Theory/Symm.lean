import Math.Algebra.Group.Theory.Basic

-- the symmetric group of α
instance Symm (α: Type*) : Group (α ≃ α) := by
  apply Group.ofAxiomsLeft .rfl .trans .symm
  intro; rfl
  intro; apply Equiv.trans_symm
  intros; rfl
