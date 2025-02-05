import Math.Data.Set.Lattice
import Math.Data.Set.Like

class IsSetLikeLattice (α: Type*) {β: outParam Type*} [Sup α] [Inf α] [LE α] [LT α] [SetLike α β] extends IsLawfulLT α: Prop where
  inf_eq_set_inf: ∀a b: α, (a ⊓ b: α) = (a ⊓ b: Set β)
  sup_eq_set_sup: ∀a b: α, (a ⊔ b: α) = (a ⊔ b: Set β)
  le_iff_sub: ∀a b: α, a ≤ b ↔ (a: Set β) ≤ b

variable [Sup α] [Inf α] [LE α] [LT α] [SetLike α β] [IsSetLikeLattice α]

def IsSetLikeLattice.OrderEmbedding : α ↪o Set β where
  toFun a := a
  inj := SetLike.coe_inj
  resp_rel := le_iff_sub _ _

instance [IsSetLikeLattice α] : IsPartialOrder α :=
  IsSetLikeLattice.OrderEmbedding.inducedIsPartialOrder'

instance [h: IsSetLikeLattice α] : IsLattice α where
  le_sup_left := by
    intro a b
    rw [h.le_iff_sub, h.sup_eq_set_sup]
    apply le_sup_left (α := Set β)
  le_sup_right := by
    intro a b
    rw [h.le_iff_sub, h.sup_eq_set_sup]
    apply le_sup_right (α := Set β)
  inf_le_left := by
    intro a b
    rw [h.le_iff_sub, h.inf_eq_set_inf]
    apply inf_le_left (α := Set β)
  inf_le_right := by
    intro a b
    rw [h.le_iff_sub, h.inf_eq_set_inf]
    apply inf_le_right (α := Set β)
  sup_le := by
    intro a b k ak bk
    rw [h.le_iff_sub] at *
    rw [h.sup_eq_set_sup]
    apply sup_le <;> assumption
  le_inf := by
    intro a b k ak bk
    rw [h.le_iff_sub] at *
    rw [h.inf_eq_set_inf]
    apply le_inf <;> assumption
