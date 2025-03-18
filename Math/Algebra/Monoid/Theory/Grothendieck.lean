import Math.Algebra.Monoid.Defs


namespace Monoid.Group

variable [MonoidOps α] [IsCommMagma α]

scoped instance : Setoid (α × α) where
  r a b := a.fst * b.snd = b.fst * a.snd
  iseqv := {
    refl _ := rfl
    symm h := h.symm
    trans := by
      sorry
  }

-- def _root_.Monoid.Group (α: Type u): Type u := Quotient

end Monoid.Group
