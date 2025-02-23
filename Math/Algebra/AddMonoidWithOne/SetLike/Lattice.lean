import Math.Data.Set.Like.Lattice
import Math.Algebra.AddMonoidWithOne.SetLike.Basic
import Math.Algebra.AddMonoidWithOne.Defs

namespace AddSubmonoidWithOne

variable [AddMonoidWithOneOps α] [IsAddMonoidWithOne α]

private instance builder : SetLike.LatticeBuilder (AddSubmonoidWithOne α) where
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
  bot := ⟨{
    carrier := Set.range (fun n: ℕ => (n: α))
    mem_zero' := ⟨0, natCast_zero.symm⟩
    mem_one' := ⟨1, natCast_one.symm⟩
    mem_add' := by
      rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
      dsimp; rw [←natCast_add]
      apply Set.mem_range'
  }, by
    intro s
    apply natRange_sub (generate s)⟩

private local instance : SetLike.CompleteLatticeLE (AddSubmonoidWithOne α) := SetLike.toCompleteLattice

instance : LE (AddSubmonoidWithOne α) := inferInstance
instance : LT (AddSubmonoidWithOne α) := inferInstance
instance : Top (AddSubmonoidWithOne α) := inferInstance
instance : Bot (AddSubmonoidWithOne α) := inferInstance
instance : Sup (AddSubmonoidWithOne α) := inferInstance
instance : Inf (AddSubmonoidWithOne α) := inferInstance
instance : SupSet (AddSubmonoidWithOne α) := inferInstance
instance : InfSet (AddSubmonoidWithOne α) := inferInstance
instance : IsPartialOrder (AddSubmonoidWithOne α) := inferInstance
instance : IsCompleteLattice (AddSubmonoidWithOne α) := inferInstance

end AddSubmonoidWithOne
