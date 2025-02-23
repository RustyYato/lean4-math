import Math.Data.Set.Like.Lattice
import Math.Algebra.Semiring.SetLike.Defs
import Math.Algebra.Semiring.Defs

import Math.Algebra.AddMonoidWithOne.SetLike.Basic

namespace Subsemiring

variable [SemiringOps α] [IsSemiring α]

private instance builder : SetLike.LatticeBuilder (Subsemiring α) where
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
    | add => apply mem_add t <;> assumption
    | mul => apply mem_mul t <;> assumption
  bot := ⟨{
    carrier := Set.range (fun n: ℕ => (n: α))
    mem_zero' := ⟨0, natCast_zero.symm⟩
    mem_one' := ⟨1, natCast_one.symm⟩
    mem_add' := by
      rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
      dsimp; rw [←natCast_add]
      apply Set.mem_range'
    mem_mul' := by
      rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
      dsimp; rw [←natCast_mul]
      apply Set.mem_range'
  }, by
    intro s
    apply natRange_sub (generate s)⟩

instance : SetLike.CompleteLatticeLE (Subsemiring α) := SetLike.toCompleteLattice

end Subsemiring
