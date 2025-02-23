import Math.Data.Set.Like.Lattice
import Math.Algebra.Field.SetLike.Defs
import Math.Algebra.Field.Defs

namespace Subfield

variable [FieldOps α] [IsField α]

private instance builder : SetLike.LatticeBuilder (Subfield α) where
  closure := (Set.mk <| Generate ·)
  closure_spec s := ⟨generate s, rfl⟩
  create s P := {
    carrier := s
    mem_zero' := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_zero s
    mem_one' := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_one s
    mem_neg' := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_neg s <;> assumption
    mem_inv?' := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_inv? s <;> assumption
    mem_add' := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_add s <;> assumption
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
    | zero => apply mem_zero t
    | one => apply mem_one t
    | neg => apply mem_neg t <;> assumption
    | inv? => apply mem_inv? t <;> assumption
    | add => apply mem_add t <;> assumption
    | mul => apply mem_mul t <;> assumption

private local instance : SetLike.CompleteLatticeLE (Subfield α) := SetLike.toCompleteLattice

instance : LE (Subfield α) := inferInstance
instance : LT (Subfield α) := inferInstance
instance : Top (Subfield α) := inferInstance
instance : Bot (Subfield α) := inferInstance
instance : Sup (Subfield α) := inferInstance
instance : Inf (Subfield α) := inferInstance
instance : SupSet (Subfield α) := inferInstance
instance : InfSet (Subfield α) := inferInstance
instance : IsPartialOrder (Subfield α) := inferInstance
instance : IsCompleteLattice (Subfield α) := inferInstance

end Subfield
