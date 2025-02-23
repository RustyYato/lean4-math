import Math.Data.Set.Like.Lattice
import Math.Algebra.Ring.SetLike.Defs
import Math.Algebra.Ring.Defs

import Math.Algebra.AddGroupWithOne.SetLike.Basic

namespace Subring

variable [RingOps α] [IsRing α]

private instance builder : SetLike.LatticeBuilder (Subring α) where
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
    | add => apply mem_add t <;> assumption
    | mul => apply mem_mul t <;> assumption
  bot := ⟨{
    carrier := Set.range (fun n: ℤ => (n: α))
    mem_zero' := ⟨0, intCast_zero.symm⟩
    mem_one' := ⟨1, intCast_one.symm⟩
    mem_neg' := by
      rintro _ ⟨n, rfl⟩
      dsimp; rw [←intCast_neg]
      apply Set.mem_range'
    mem_add' := by
      rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
      dsimp; rw [←intCast_add]
      apply Set.mem_range'
    mem_mul' := by
      rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
      dsimp; rw [←intCast_mul]
      apply Set.mem_range'
  }, by
    intro s
    apply intRange_sub (generate s)⟩

private local instance : SetLike.CompleteLatticeLE (Subring α) := SetLike.toCompleteLattice

instance : LE (Subring α) := inferInstance
instance : LT (Subring α) := inferInstance
instance : Top (Subring α) := inferInstance
instance : Bot (Subring α) := inferInstance
instance : Sup (Subring α) := inferInstance
instance : Inf (Subring α) := inferInstance
instance : SupSet (Subring α) := inferInstance
instance : InfSet (Subring α) := inferInstance
instance : IsPartialOrder (Subring α) := inferInstance
instance : IsCompleteLattice (Subring α) := inferInstance

end Subring
