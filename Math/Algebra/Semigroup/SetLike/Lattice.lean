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
    mem_mul' := by
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

instance : SetLike.CompleteLatticeLE (Subsemigroup α) := SetLike.toCompleteLattice

end Subsemigroup

namespace AddSubsemigroup

variable [Add α]

private instance builder : SetLike.LatticeBuilder (AddSubsemigroup α) where
  closure := (Set.mk <| Generate ·)
  closure_spec s := ⟨generate s, rfl⟩
  create s P := {
    carrier := s
    mem_add' := by
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

instance : SetLike.CompleteLatticeLE (AddSubsemigroup α) := SetLike.toCompleteLattice

end AddSubsemigroup
