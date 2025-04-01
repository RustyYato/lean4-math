import Math.Data.Set.Like.Lattice
import Math.Algebra.Semigroup.SetLike.Defs
import Math.Algebra.Semigroup.Defs

namespace Subsemigroup

variable [Mul α]

private instance builder : SetLike.LatticeBuilder (Subsemigroup α) where
  closure := (Set.mk <| Generate ·)
  closure_spec s := ⟨generate s, rfl⟩
  create s P := {
    carrier := s
    mem_mul := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_mul s <;> assumption
  }
  gc := by
    intro s t
    apply flip Iff.intro
    intro h x hx
    apply h
    apply Generate.of
    assumption
    intro h x hx
    induction hx with
    | of => apply h; assumption
    | mul => apply mem_mul t <;> assumption
  bot := ⟨⟨∅, fun h => False.elim h⟩, fun _ => Set.empty_sub _⟩

private local instance : SetLike.CompleteLatticeLE (Subsemigroup α) := SetLike.toCompleteLattice

instance : LE (Subsemigroup α) := inferInstance
instance : LT (Subsemigroup α) := inferInstance
instance : Top (Subsemigroup α) := inferInstance
instance : Bot (Subsemigroup α) := inferInstance
instance : Max (Subsemigroup α) := inferInstance
instance : Min (Subsemigroup α) := inferInstance
instance : SupSet (Subsemigroup α) := inferInstance
instance : InfSet (Subsemigroup α) := inferInstance
instance : IsPartialOrder (Subsemigroup α) := inferInstance
instance : IsCompleteLattice (Subsemigroup α) := inferInstance

end Subsemigroup

namespace AddSubsemigroup

variable [Add α]

private instance builder : SetLike.LatticeBuilder (AddSubsemigroup α) where
  closure := (Set.mk <| Generate ·)
  closure_spec s := ⟨generate s, rfl⟩
  create s P := {
    carrier := s
    mem_add := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_add s <;> assumption
  }
  gc := by
    intro s t
    apply flip Iff.intro
    intro h x hx
    apply h
    apply Generate.of
    assumption
    intro h x hx
    induction hx with
    | of => apply h; assumption
    | add => apply mem_add t <;> assumption
  bot := ⟨⟨∅, fun h => False.elim h⟩, fun _ => Set.empty_sub _⟩

private local instance : SetLike.CompleteLatticeLE (AddSubsemigroup α) := SetLike.toCompleteLattice

instance : LE (AddSubsemigroup α) := inferInstance
instance : LT (AddSubsemigroup α) := inferInstance
instance : Top (AddSubsemigroup α) := inferInstance
instance : Bot (AddSubsemigroup α) := inferInstance
instance : Max (AddSubsemigroup α) := inferInstance
instance : Min (AddSubsemigroup α) := inferInstance
instance : SupSet (AddSubsemigroup α) := inferInstance
instance : InfSet (AddSubsemigroup α) := inferInstance
instance : IsPartialOrder (AddSubsemigroup α) := inferInstance
instance : IsCompleteLattice (AddSubsemigroup α) := inferInstance

end AddSubsemigroup
