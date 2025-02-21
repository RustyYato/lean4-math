import Math.Order.Linear
import Math.Order.OrderIso

namespace OrderEmbedding

def inducedIsLinearOrder {_: LE α} [LT α] {_: LE β} [LT β]
  [_root_.IsLinearOrder β]
  [IsLawfulLT α]
  (h: α ↪o β)
  : _root_.IsLinearOrder α :=
  have := h.inducedIsPartialOrder'
  {
    le_antisymm := le_antisymm
    le_trans := le_trans
    lt_or_le := by
      intro a b
      rcases lt_or_le (h a) (h b) with g | g
      exact .inl (h.resp_lt.mpr g)
      exact .inr (h.resp_le.mpr g)
  }

end OrderEmbedding

namespace OrderIso

def instIsLinearOrder {_: LE α} [LT α] {_: LE β} [LT β]
  [_root_.IsLinearOrder β]
  [IsLawfulLT α]
  (h: α ≃o β)
  : _root_.IsLinearOrder α := h.toEmbedding.inducedIsLinearOrder

def instIsLinearMinMaxOrder {_: LE α} [LT α] {_: LE β} [LT β]
  [Min α] [Min β] [Max α] [Max β]
  [IsLinearMinMaxOrder β]
  [IsLawfulLT α]
  (h: α ≃o β)
  (min_eq: ∀a b: α, min a b = h.symm (min (h a) (h b)))
  (max_eq: ∀a b: α, max a b = h.symm (max (h a) (h b)))
  : _root_.IsLinearMinMaxOrder α :=
  {
    toIsLinearOrder := h.instIsLinearOrder
    min_iff_le_left := by
      intro a b
      rw [h.resp_le, min_eq, ←Function.Injective.eq_iff h.inj]
      show _ ↔ h (h.symm _) = _
      rw [h.symm_coe]; apply min_iff_le_left
    min_iff_le_right := by
      intro a b
      rw [h.resp_le, min_eq, ←Function.Injective.eq_iff h.inj]
      show _ ↔ h (h.symm _) = _
      rw [h.symm_coe]; apply min_iff_le_right
    max_iff_le_left := by
      intro a b
      rw [h.resp_le, max_eq, ←Function.Injective.eq_iff h.inj]
      show _ ↔ h (h.symm _) = _
      rw [h.symm_coe]; apply max_iff_le_left
    max_iff_le_right := by
      intro a b
      rw [h.resp_le, max_eq, ←Function.Injective.eq_iff h.inj]
      show _ ↔ h (h.symm _) = _
      rw [h.symm_coe]; apply max_iff_le_right
  }

def instIsDecidableLinearOrder {_: LE α} [LT α] {_: LE β} [LT β]
  [Min α] [Min β] [Max α] [Max β]
  [IsDecidableLinearOrder β]
  [IsLawfulLT α]
  (h: α ≃o β)
  (min_eq: ∀a b: α, min a b = h.symm (min (h a) (h b)))
  (max_eq: ∀a b: α, max a b = h.symm (max (h a) (h b)))
  : _root_.IsDecidableLinearOrder α :=
  {
    toIsLinearMinMaxOrder := h.instIsLinearMinMaxOrder min_eq max_eq
    min_def := by
      intro a b
      rw [min_eq, min_def]
      split
      rw [←h.resp_le] at *
      rw [if_pos, h.coe_symm]; assumption
      rw [←h.resp_le] at *
      rw [if_neg, h.coe_symm]; assumption
    max_def := by
      intro a b
      rw [max_eq, max_def]
      split
      rw [←h.resp_le] at *
      rw [if_pos, h.coe_symm]; assumption
      rw [←h.resp_le] at *
      rw [if_neg, h.coe_symm]; assumption
    decLE a b := decidable_of_iff (h a ≤ h b) h.resp_le.symm
  }

end OrderIso
