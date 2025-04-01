import Math.Data.Set.Like.Lattice
import Math.Algebra.Monoid.SetLike.Defs
import Math.Algebra.Monoid.Defs

namespace Submonoid

variable [MonoidOps α] [IsMonoid α]

private instance builder : SetLike.LatticeBuilder (Submonoid α) where
  closure := (Set.mk <| Generate ·)
  closure_spec s := ⟨generate s, rfl⟩
  create s P := {
    carrier := s
    mem_one := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_one s
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
    | one => apply mem_one t
    | mul => apply mem_mul t <;> assumption
  bot := ⟨{
    carrier := {1}
    mem_one := rfl
    mem_mul := by
      rintro _ _ rfl rfl
      rw [mul_one]; rfl
  }, by rintro _ _ rfl; apply Generate.one⟩

private local instance : SetLike.CompleteLatticeLE (Submonoid α) := SetLike.toCompleteLattice

instance : LE (Submonoid α) := inferInstance
instance : LT (Submonoid α) := inferInstance
instance : Top (Submonoid α) := inferInstance
instance : Bot (Submonoid α) := inferInstance
instance : Max (Submonoid α) := inferInstance
instance : Min (Submonoid α) := inferInstance
instance : SupSet (Submonoid α) := inferInstance
instance : InfSet (Submonoid α) := inferInstance
instance : IsPartialOrder (Submonoid α) := inferInstance
instance : IsCompleteLattice (Submonoid α) := inferInstance

end Submonoid

namespace AddSubmonoid

variable [AddMonoidOps α] [IsAddMonoid α]

private instance builder : SetLike.LatticeBuilder (AddSubmonoid α) where
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
  bot := ⟨{
    carrier := {0}
    mem_zero := rfl
    mem_add := by
      rintro _ _ rfl rfl
      rw [add_zero]; rfl
  }, by rintro _ _ rfl; apply Generate.zero⟩

private local instance : SetLike.CompleteLatticeLE (AddSubmonoid α) := SetLike.toCompleteLattice

instance : LE (AddSubmonoid α) := inferInstance
instance : LT (AddSubmonoid α) := inferInstance
instance : Top (AddSubmonoid α) := inferInstance
instance : Bot (AddSubmonoid α) := inferInstance
instance : Max (AddSubmonoid α) := inferInstance
instance : Min (AddSubmonoid α) := inferInstance
instance : SupSet (AddSubmonoid α) := inferInstance
instance : InfSet (AddSubmonoid α) := inferInstance
instance : IsPartialOrder (AddSubmonoid α) := inferInstance
instance : IsCompleteLattice (AddSubmonoid α) := inferInstance

end AddSubmonoid
