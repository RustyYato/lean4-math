import Math.Algebra.Con.Defs
import Math.Relation.Lattice
import Math.Order.GaloisConnection

namespace AddCon

variable [Add α]

def giConnection : @GaloisInsertion (α -> α -> Prop) (AddCon α) _ _ (fun r => generate r) (fun r => r.r) where
  gc a b := by
    apply Iff.intro
    intro h
    apply le_trans
    apply le_generate
    assumption
    intro h
    apply ofGenerate a b
    assumption
  le_l_u a := by apply le_generate
  choice r h := copy (generate r) r <| by
    apply le_antisymm
    apply le_generate
    assumption
  choice_eq r h := by
    simp
    apply le_antisymm
    apply le_generate
    assumption

instance : CompleteLattice (AddCon α) := {
  giConnection.liftCompleteLattice with
  bot := {
    r := (· = ·)
    iseqv := Relation.equiv _
    resp_add := by
      rintro _ _ _ _ rfl rfl
      rfl
  }
  bot_le r a b := by
    rintro rfl
    rfl
}

end AddCon

namespace MulCon

variable [Mul α]

def giConnection : @GaloisInsertion (α -> α -> Prop) (MulCon α) _ _ (fun r => generate r) (fun r => r.r) where
  gc a b := by
    apply Iff.intro
    intro h
    apply le_trans
    apply le_generate
    assumption
    intro h
    apply ofGenerate a b
    assumption
  le_l_u a := by apply le_generate
  choice r h := copy (generate r) r <| by
    apply le_antisymm
    apply le_generate
    assumption
  choice_eq r h := by
    simp
    apply le_antisymm
    apply le_generate
    assumption

instance : CompleteLattice (MulCon α) := {
  giConnection.liftCompleteLattice with
  bot := {
    r := (· = ·)
    iseqv := Relation.equiv _
    resp_mul := by
      rintro _ _ _ _ rfl rfl
      rfl
  }
  bot_le r a b := by
    rintro rfl
    rfl
}

end MulCon

namespace RingCon

variable [Add α] [Mul α]

def giConnection : @GaloisInsertion (α -> α -> Prop) (RingCon α) _ _ (fun r => generate r) (fun r => r.r) where
  gc a b := by
    apply Iff.intro
    intro h
    apply le_trans
    apply le_generate
    assumption
    intro h
    apply ofGenerate a b
    assumption
  le_l_u a := by apply le_generate
  choice r h := copy (generate r) r <| by
    apply le_antisymm
    apply le_generate
    assumption
  choice_eq r h := by
    simp
    apply le_antisymm
    apply le_generate
    assumption

instance : CompleteLattice (RingCon α) := {
  giConnection.liftCompleteLattice with
  bot := {
    r := (· = ·)
    iseqv := Relation.equiv _
    resp_add := by
      rintro _ _ _ _ rfl rfl
      rfl
    resp_mul := by
      rintro _ _ _ _ rfl rfl
      rfl
  }
  bot_le r a b := by
    rintro rfl
    rfl
}

end RingCon
