import Math.Data.Set.Like.Lattice
import Math.Algebra.GroupWithZero.SetLike.Basic
import Math.Algebra.GroupWithZero.Basic

namespace SubgroupWithZero

variable [GroupWithZeroOps α] [IsGroupWithZero α]

private instance builder : SetLike.LatticeBuilder (SubgroupWithZero α) where
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
    mem_inv?' := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_inv? s <;> assumption
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
    | mul => apply mem_mul t <;> assumption
  bot := ⟨{
    carrier := {0, 1}
    mem_zero := by simp
    mem_one := by simp
    mem_inv?' := by
      rintro _ _ h
      simp at *
      cases h; contradiction
      right; rename_i h; subst h
      rw [inv?_one]
    mem_mul := by
      rintro _ _ h g
      simp at *
      rcases h with rfl | rfl
      left; rw [zero_mul]
      rcases g with rfl | rfl
      left; rw [mul_zero]
      right; rw [mul_one]
  }, by
    rintro _ x h
    rcases h with rfl | rfl
    apply Generate.zero
    apply Generate.one⟩

private local instance : SetLike.CompleteLatticeLE (SubgroupWithZero α) := SetLike.toCompleteLattice

instance : LE (SubgroupWithZero α) := inferInstance
instance : LT (SubgroupWithZero α) := inferInstance
instance : Top (SubgroupWithZero α) := inferInstance
instance : Bot (SubgroupWithZero α) := inferInstance
instance : Sup (SubgroupWithZero α) := inferInstance
instance : Inf (SubgroupWithZero α) := inferInstance
instance : SupSet (SubgroupWithZero α) := inferInstance
instance : InfSet (SubgroupWithZero α) := inferInstance
instance : IsPartialOrder (SubgroupWithZero α) := inferInstance
instance : IsCompleteLattice (SubgroupWithZero α) := inferInstance

end SubgroupWithZero
