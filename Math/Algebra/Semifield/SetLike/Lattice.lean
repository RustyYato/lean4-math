import Math.Data.Set.Like.Lattice
import Math.Algebra.Semifield.SetLike.Defs
import Math.Algebra.Semifield.Defs

namespace Subsemifield

variable [SemifieldOps α] [IsSemifield α]

private instance builder : SetLike.LatticeBuilder (Subsemifield α) where
  closure := (Set.mk <| Generate ·)
  closure_spec s := ⟨generate s, rfl⟩
  create s P := {
    carrier := s
    mem_zero := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_zero s
    mem_one := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_one s
    mem_inv? := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_inv? s <;> assumption
    mem_add := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_add s <;> assumption
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
    | zero => apply mem_zero t
    | one => apply mem_one t
    | inv? => apply mem_inv? t <;> assumption
    | add => apply mem_add t <;> assumption
    | mul => apply mem_mul t <;> assumption

private local instance : SetLike.CompleteLatticeLE (Subsemifield α) := SetLike.toCompleteLattice

instance : LE (Subsemifield α) := inferInstance
instance : LT (Subsemifield α) := inferInstance
instance : Top (Subsemifield α) := inferInstance
instance : Bot (Subsemifield α) := inferInstance
instance : Max (Subsemifield α) := inferInstance
instance : Min (Subsemifield α) := inferInstance
instance : SupSet (Subsemifield α) := inferInstance
instance : InfSet (Subsemifield α) := inferInstance
instance : IsPartialOrder (Subsemifield α) := inferInstance
instance : IsCompleteLattice (Subsemifield α) := inferInstance

end Subsemifield
