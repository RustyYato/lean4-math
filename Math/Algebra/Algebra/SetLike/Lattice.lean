import Math.Data.Set.Like.Lattice
import Math.Algebra.Algebra.SetLike.Defs
import Math.Algebra.Algebra.Defs

import Math.Algebra.AddGroupWithOne.SetLike.Basic

namespace Subring

variable [SemiringOps R] [IsSemiring R] [SemiringOps α] [IsSemiring α] [AlgebraMap R α]

private instance builder : SetLike.LatticeBuilder (Subalgebra R α) where
  closure := (Set.mk <| Generate R ·)
  closure_spec s := ⟨generate R s, rfl⟩
  create s P := {
    carrier := s
    mem_algebraMap := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_algebraMap R s
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
    | algebraMap => apply mem_algebraMap R t
    | add => apply mem_add t <;> assumption
    | mul => apply mem_mul t <;> assumption
  bot := ⟨{
    carrier := Set.range (algebraMap (R := R))
    mem_algebraMap _ := Set.mem_range'
    mem_add := by
      rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
      rw [←map_add]; apply Set.mem_range'
    mem_mul := by
      rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
      rw [←map_mul]; apply Set.mem_range'
  }, by
    intro s
    rintro _ ⟨r, rfl⟩
    apply Generate.algebraMap⟩

private local instance : SetLike.CompleteLatticeLE (Subalgebra R α) := SetLike.toCompleteLattice

instance : LE (Subalgebra R α) := inferInstance
instance : LT (Subalgebra R α) := inferInstance
instance : Top (Subalgebra R α) := inferInstance
instance : Bot (Subalgebra R α) := inferInstance
instance : Max (Subalgebra R α) := inferInstance
instance : Min (Subalgebra R α) := inferInstance
instance : SupSet (Subalgebra R α) := inferInstance
instance : InfSet (Subalgebra R α) := inferInstance
instance : IsPartialOrder (Subalgebra R α) := inferInstance
instance : IsCompleteLattice (Subalgebra R α) := inferInstance

end Subring
