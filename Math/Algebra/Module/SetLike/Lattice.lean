import Math.Data.Set.Like.Lattice
import Math.Algebra.Module.SetLike.Defs
import Math.Algebra.Module.Defs

namespace Submodule

variable [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M] [SMul R M] [IsModule R M]

private instance builder : SetLike.LatticeBuilder (Submodule R M) where
  closure := (Set.mk <| Generate ·)
  closure_spec s := ⟨generate s, rfl⟩
  create s P := {
    carrier := s
    mem_zero := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_zero s
    mem_add := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_add s <;> assumption
    mem_smul' := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_smul s <;> assumption
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
    | add => apply mem_add t <;> assumption
    | smul => apply mem_smul t <;> assumption
  bot := ⟨{
    carrier := {0}
    mem_zero := rfl
    mem_add := by
      rintro _ _ rfl rfl
      rw [add_zero]; rfl
    mem_smul' := by
      rintro _ _ rfl
      rw [smul_zero]; rfl
  }, by rintro _ _ rfl; apply Generate.zero⟩

private local instance : SetLike.CompleteLatticeLE (Submodule R M) := SetLike.toCompleteLattice

instance : LE (Submodule R M) := inferInstance
instance : LT (Submodule R M) := inferInstance
instance : Top (Submodule R M) := inferInstance
instance : Bot (Submodule R M) := inferInstance
instance : Sup (Submodule R M) := inferInstance
instance : Inf (Submodule R M) := inferInstance
instance : SupSet (Submodule R M) := inferInstance
instance : InfSet (Submodule R M) := inferInstance
instance : IsPartialOrder (Submodule R M) := inferInstance
instance : IsCompleteLattice (Submodule R M) := inferInstance

end Submodule
