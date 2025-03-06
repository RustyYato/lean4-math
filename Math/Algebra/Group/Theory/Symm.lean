import Math.Algebra.Group.Theory.Basic

-- the symmetric group of α
instance Symm (α: Type*) : Group (α ≃ α) := by
  apply Group.ofAxiomsLeft .rfl .trans .symm
  intro; rfl
  intro; apply Equiv.trans_symm
  intros; rfl

def embed_symm_group (α: Type*) [DecidableEq α] [GroupOps α] [IsGroup α] : α ↪ Symm α where
  toFun a := Equiv.swap 1 a
  inj' := by
    intro a b eq
    dsimp at eq
    have : Equiv.swap 1 a 1 = Equiv.swap  1 b 1 := by rw [eq]
    rw [Equiv.swap_spec, Equiv.swap_spec] at this
    assumption
