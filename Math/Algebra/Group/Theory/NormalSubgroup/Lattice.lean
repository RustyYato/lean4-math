import Math.Algebra.Group.Theory.NormalSubgroup.Basic
import Math.Data.Set.Like.Lattice
import Math.Algebra.Group.SetLike.Defs
import Math.Algebra.Group.Defs

namespace NormalSubgroup

variable [GroupOps α] [IsGroup α]

private instance builder : SetLike.LatticeBuilder (NormalSubgroup α) where
  closure := (Set.mk <| Generate ·)
  closure_spec s := ⟨generate s, rfl⟩
  create s P := {
    carrier := s
    mem_conj := by
      obtain ⟨s, rfl⟩ := P
      intros; apply mem_conj s <;> assumption
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
    | conj => apply mem_conj t <;> assumption
  bot := ⟨{
    carrier := {1}
    mem_one := rfl
    mem_mul := by
      rintro _ _ rfl rfl
      rw [mul_one]; rfl
    mem_inv := by
      rintro _ rfl
      rw [inv_one]; rfl
    mem_conj := by
      rintro _ _ rfl
      rw [map_one]; rfl
  }, by rintro _ _ rfl; apply Generate.one⟩

private local instance : SetLike.CompleteLatticeLE (NormalSubgroup α) := SetLike.toCompleteLattice

instance : LE (NormalSubgroup α) := inferInstance
instance : LT (NormalSubgroup α) := inferInstance
instance : Top (NormalSubgroup α) := inferInstance
instance : Bot (NormalSubgroup α) := inferInstance
instance : Max (NormalSubgroup α) := inferInstance
instance : Min (NormalSubgroup α) := inferInstance
instance : SupSet (NormalSubgroup α) := inferInstance
instance : InfSet (NormalSubgroup α) := inferInstance
instance : IsPartialOrder (NormalSubgroup α) := inferInstance
instance : IsCompleteLattice (NormalSubgroup α) := inferInstance

end NormalSubgroup
