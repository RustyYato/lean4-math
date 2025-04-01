import Math.Data.Set.Like.Lattice
import Math.Algebra.Group.SetLike.Defs
import Math.Algebra.Group.Defs

namespace Subgroup

variable [GroupOps α] [IsGroup α]

private instance builder : SetLike.LatticeBuilder (Subgroup α) where
  closure := (Set.mk <| Generate ·)
  closure_spec s := ⟨generate s, rfl⟩
  create s P := {
    carrier := s
    mem_mul := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_mul s <;> assumption
    mem_inv := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_inv s <;> assumption
    mem_one := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_one s
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
    | inv => apply mem_inv t <;> assumption
    | mul => apply mem_mul t <;> assumption
  bot := ⟨{
    carrier := {1}
    mem_one := rfl
    mem_mul := by
      rintro _ _ rfl rfl
      rw [mul_one]; rfl
    mem_inv := by
      rintro _ rfl
      rw [inv_one]; rfl
  }, by rintro _ _ rfl; apply Generate.one⟩

private local instance : SetLike.CompleteLatticeLE (Subgroup α) := SetLike.toCompleteLattice

instance : LE (Subgroup α) := inferInstance
instance : LT (Subgroup α) := inferInstance
instance : Top (Subgroup α) := inferInstance
instance : Bot (Subgroup α) := inferInstance
instance : Sup (Subgroup α) := inferInstance
instance : Inf (Subgroup α) := inferInstance
instance : SupSet (Subgroup α) := inferInstance
instance : InfSet (Subgroup α) := inferInstance
instance : IsPartialOrder (Subgroup α) := inferInstance
instance : IsCompleteLattice (Subgroup α) := inferInstance

end Subgroup

namespace AddSubgroup

variable [AddGroupOps α] [IsAddGroup α]

private instance builder : SetLike.LatticeBuilder (AddSubgroup α) where
  closure := (Set.mk <| Generate ·)
  closure_spec s := ⟨generate s, rfl⟩
  create s P := {
    carrier := s
    mem_add := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_add s <;> assumption
    mem_neg := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_neg s <;> assumption
    mem_zero := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_zero s
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
    | neg => apply mem_neg t <;> assumption
    | add => apply mem_add t <;> assumption
  bot := ⟨{
    carrier := {0}
    mem_zero := rfl
    mem_neg := by
      rintro _ rfl
      rw [neg_zero]; rfl
    mem_add := by
      rintro _ _ rfl rfl
      rw [add_zero]; rfl
  }, by rintro _ _ rfl; apply Generate.zero⟩

private local instance : SetLike.CompleteLatticeLE (AddSubgroup α) := SetLike.toCompleteLattice

instance : LE (AddSubgroup α) := inferInstance
instance : LT (AddSubgroup α) := inferInstance
instance : Top (AddSubgroup α) := inferInstance
instance : Bot (AddSubgroup α) := inferInstance
instance : Sup (AddSubgroup α) := inferInstance
instance : Inf (AddSubgroup α) := inferInstance
instance : SupSet (AddSubgroup α) := inferInstance
instance : InfSet (AddSubgroup α) := inferInstance
instance : IsPartialOrder (AddSubgroup α) := inferInstance
instance : IsCompleteLattice (AddSubgroup α) := inferInstance

end AddSubgroup
