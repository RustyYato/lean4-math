import Math.Data.Set.Lattice
import Math.Data.Set.Like

class IsSetLikeLattice (α: Type*) {β: outParam Type*} [Max α] [Min α] [LE α] [LT α] [SetLike α β] : Prop extends IsLawfulLT α where
  min_eq_set_min: ∀a b: α, (a ⊓ b: α) = (a ⊓ b: Set β)
  max_eq_set_max: ∀a b: α, (a ⊔ b: α) = (a ⊔ b: Set β)
  le_iff_sub: ∀a b: α, a ≤ b ↔ (a: Set β) ≤ b

variable [Max α] [Min α] [LE α] [LT α] [SetLike α β] [IsSetLikeLattice α]

def IsSetLikeLattice.OrderEmbedding : α ↪o Set β where
  toFun a := a
  inj' := SetLike.coe_inj
  resp_rel := le_iff_sub _ _

instance [IsSetLikeLattice α] : IsPartialOrder α :=
  IsSetLikeLattice.OrderEmbedding.instIsPartialOrder'

instance [h: IsSetLikeLattice α] : IsLattice α where
  le_max_left := by
    intro a b
    rw [h.le_iff_sub, h.max_eq_set_max]
    apply le_max_left (α := Set β)
  le_max_right := by
    intro a b
    rw [h.le_iff_sub, h.max_eq_set_max]
    apply le_max_right (α := Set β)
  min_le_left := by
    intro a b
    rw [h.le_iff_sub, h.min_eq_set_min]
    apply min_le_left (α := Set β)
  min_le_right := by
    intro a b
    rw [h.le_iff_sub, h.min_eq_set_min]
    apply min_le_right (α := Set β)
  max_le := by
    intro a b k ak bk
    rw [h.le_iff_sub] at *
    rw [h.max_eq_set_max]
    apply max_le <;> assumption
  le_min := by
    intro a b k ak bk
    rw [h.le_iff_sub] at *
    rw [h.min_eq_set_min]
    apply le_min <;> assumption
