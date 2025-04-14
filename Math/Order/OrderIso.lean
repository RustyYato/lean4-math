import Math.Relation.RelIso
import Math.Logic.Equiv.Like
import Math.Order.Defs
import Math.Order.Hom.Defs

variable {α β: Type*} [LE α] [LT α] [LE β] [LT β]

section

def instIsPreOrder {_: LE α} [LT α] {_: LE β} [LT β]
  [IsPreOrder β] [IsLawfulLT α]
  [EmbeddingLike F α β] [IsOrderHom F α β]
  (h: F)
  : IsPreOrder α where
  le_refl x := (map_le h).mpr (le_refl _)
  le_trans := by
    intro a b c
    iterate 3 rw [map_le h]
    exact le_trans

def instIsPartialOrder {_: LE α} [LT α] {_: LE β} [LT β]
  [IsPartialOrder β] [_root_.IsPreOrder α]
  [EmbeddingLike F α β] [IsOrderHom F α β]
  (h: F)
  : IsPartialOrder α where
  le_antisymm := by
    intro a b
    iterate 2 rw [map_le h]
    intro ab ba
    have := le_antisymm ab ba
    exact (h: α ↪ β).inj this

def instIsPartialOrder' {_: LE α} [LT α] {_: LE β} [LT β]
  [_root_.IsPartialOrder β] [IsLawfulLT α]
  [EmbeddingLike F α β] [IsOrderHom F α β]
  (h: F)
  : _root_.IsPartialOrder α where
  toIsPreOrder := instIsPreOrder h
  le_antisymm := by
    intro a b
    rw [map_le h, map_le h]
    intro ab ba
    exact (h: α ↪ β).inj (le_antisymm ab ba)

def instIsLinearOrder {_: LE α} [LT α] {_: LE β} [LT β]
  [_root_.IsLinearOrder β] [IsLawfulLT α]
  [EmbeddingLike F α β] [IsOrderHom F α β]
  (h: F)
  : _root_.IsLinearOrder α :=
  have := instIsPartialOrder' h
  {
    le_antisymm := le_antisymm
    le_trans := le_trans
    lt_or_le := by
      intro a b
      rcases lt_or_le (h a) (h b) with g | g
      exact .inl ((map_lt h).mpr g)
      exact .inr ((map_le h).mpr g)
  }

def instIsSemiLatticeMax
  [LE α] [LT α] [Max α]
  [LE β] [LT β] [Max β]
  [IsSemiLatticeMax α] [_root_.IsPartialOrder β]
  [EmbeddingLike F β α] [IsOrderHom F β α] [IsMaxHom F β α]
  (h: F): IsSemiLatticeMax β where
  le_max_left := by
    intro a b
    have : h a ≤ h a ⊔ h b := le_max_left _ _
    rw [←map_max] at this
    exact (map_le h).mpr this
  le_max_right := by
    intro a b
    have : h b ≤ h a ⊔ h b := le_max_right _ _
    rw [←map_max] at this
    exact (map_le h).mpr this
  max_le := by
    intro a b k ak bk
    replace ak := (map_le h).mp ak
    replace bk := (map_le h).mp bk
    have := max_le ak bk
    rw [←map_max] at this
    exact (map_le h).mpr this

def instIsSemiLatticeMin
  {α}
  [LE α] [LT α] [Min α]
  [LE β] [LT β] [Min β]
  [IsSemiLatticeMin α] [_root_.IsPartialOrder β]
  [EmbeddingLike F β α] [IsOrderHom F β α] [IsMinHom F β α]
  (h: F): IsSemiLatticeMin β where
  min_le_left := by
    intro a b
    have : h a ⊓ h b ≤ h a := min_le_left _ _
    rw [←map_min] at this
    exact (map_le h).mpr this
  min_le_right := by
    intro a b
    have : h a ⊓ h b ≤ h b := min_le_right _ _
    rw [←map_min] at this
    exact (map_le h).mpr this
  le_min := by
    intro a b k ak bk
    replace ak := (map_le h).mp ak
    replace bk := (map_le h).mp bk
    have := le_min ak bk
    rw [←map_min] at this
    exact (map_le h).mpr this

def instIsLattice {_: LE α} [LT α] {_: LE β} [LT β]
  [Min α] [Min β] [Max α] [Max β]
  [IsLattice β]
  [IsLawfulLT α]
  [EmbeddingLike F α β] [IsOrderHom F α β] [IsMinHom F α β] [IsMaxHom F α β]
  (h: F)
  : IsLattice α :=
  have := instIsPartialOrder' h
  {
    instIsSemiLatticeMax h, instIsSemiLatticeMin h with
  }

def instIsLinearLattice {_: LE α} [LT α] {_: LE β} [LT β]
  [Min α] [Min β] [Max α] [Max β]
  [IsLinearLattice β]
  [IsLawfulLT α]
  [EmbeddingLike F α β] [IsOrderHom F α β] [IsMinHom F α β] [IsMaxHom F α β]
  (h: F)
  : IsLinearLattice α := { instIsLinearOrder h, instIsLattice h with }

def instIsDecidableLinearOrder {_: LE α} [LT α] {_: LE β} [LT β]
  [Min α] [Min β] [Max α] [Max β]
  [IsDecidableLinearOrder β]
  [IsLawfulLT α]
  [EmbeddingLike F α β] [IsOrderHom F α β] [IsMinHom F α β] [IsMaxHom F α β]
  (h: F)
  : IsDecidableLinearOrder α :=
  have := instIsLinearLattice h
  {
    decLE a b := decidable_of_iff (h a ≤ h b) <| (map_le h).symm
    min_def a b := by
      split
      rwa [min_eq_left]
      rw [min_eq_right]
      apply le_of_not_le
      assumption
    max_def a b := by
      split
      rwa [max_eq_right]
      rw [max_eq_left]
      apply le_of_not_le
      assumption
  }

end

namespace OrderEmbedding

def instIsPreOrder {_: LE α} [LT α] {_: LE β} [LT β]
  [IsPreOrder β]
  [IsLawfulLT α]
  (h: α ↪o β)
  : IsPreOrder α where
  le_refl x := (map_le h).mpr (le_refl _)
  le_trans := by
    intro a b c
    iterate 3 rw [map_le h]
    exact le_trans

def instIsPartialOrder {_: LE α} [LT α] {_: LE β} [LT β]
  [IsPartialOrder β]
  [_root_.IsPreOrder α]
  (h: α ↪o β)
  : IsPartialOrder α where
  le_antisymm := by
    intro a b
    iterate 2 rw [map_le h]
    intro ab ba
    have := le_antisymm ab ba
    exact h.inj this

def instIsPartialOrder' {_: LE α} [LT α] {_: LE β} [LT β]
  [_root_.IsPartialOrder β]
  [IsLawfulLT α]
  (h: α ↪o β)
  : _root_.IsPartialOrder α where
  toIsPreOrder := h.instIsPreOrder
  le_antisymm := by
    intro a b
    rw [map_le h, map_le h]
    intro ab ba
    exact h.inj (le_antisymm ab ba)

def instIsLinearOrder {_: LE α} [LT α] {_: LE β} [LT β]
  [_root_.IsLinearOrder β]
  [IsLawfulLT α]
  (h: α ↪o β)
  : _root_.IsLinearOrder α :=
  have := h.instIsPartialOrder'
  {
    le_antisymm := le_antisymm
    le_trans := le_trans
    lt_or_le := by
      intro a b
      rcases lt_or_le (h a) (h b) with g | g
      exact .inl ((map_lt h).mpr g)
      exact .inr ((map_le h).mpr g)
  }

def instIsLawfulTop {_: LE α} [LT α] {_: LE β} [LT β]
  [Top α] [Top β]
  [IsLawfulTop β]
  (h: α ↪o β) (map_top: h ⊤ = ⊤) : IsLawfulTop α where
  le_top := by
    intro x
    apply (map_le h).mpr
    rw [map_top]
    apply le_top

def instIsLawfulBot {_: LE α} [LT α] {_: LE β} [LT β]
  [Bot α] [Bot β]
  [IsLawfulBot β]
  (h: α ↪o β) (map_bot: h ⊥ = ⊥) : IsLawfulBot α where
  bot_le := by
    intro x
    apply (map_le h).mpr
    rw [map_bot]
    apply bot_le

def instIsSemiLatticeMax
  {α}
  [LE α] [LT α] [Max α]
  [LE β] [LT β] [Max β]
  [IsSemiLatticeMax α]
  [_root_.IsPartialOrder β]
  (h: β ↪o α)
  (hs: ∀a b, h (a ⊔ b) = h a ⊔ h b): IsSemiLatticeMax β where
  le_max_left := by
    intro a b
    have : h a ≤ h a ⊔ h b := le_max_left _ _
    rw [←hs] at this
    exact (map_le h).mpr this
  le_max_right := by
    intro a b
    have : h b ≤ h a ⊔ h b := le_max_right _ _
    rw [←hs] at this
    exact (map_le h).mpr this
  max_le := by
    intro a b k ak bk
    replace ak := (map_le h).mp ak
    replace bk := (map_le h).mp bk
    have := max_le ak bk
    rw [←hs] at this
    exact (map_le h).mpr this

def instIsSemiLatticeMin
  {α}
  [LE α] [LT α] [Min α]
  [LE β] [LT β] [Min β]
  [IsSemiLatticeMin α]
  [_root_.IsPartialOrder β]
  (h: β ↪o α)
  (hs: ∀a b, h (a ⊓ b) = h a ⊓ h b): IsSemiLatticeMin β where
  min_le_left := by
    intro a b
    have : h a ⊓ h b ≤ h a := min_le_left _ _
    rw [←hs] at this
    exact (map_le h).mpr this
  min_le_right := by
    intro a b
    have : h a ⊓ h b ≤ h b := min_le_right _ _
    rw [←hs] at this
    exact (map_le h).mpr this
  le_min := by
    intro a b k ak bk
    replace ak := (map_le h).mp ak
    replace bk := (map_le h).mp bk
    have := le_min ak bk
    rw [←hs] at this
    exact (map_le h).mpr this

def instIsLinearLattice {_: LE α} [LT α] {_: LE β} [LT β]
  [Min α] [Min β] [Max α] [Max β]
  [IsLinearLattice β]
  [IsLawfulLT α]
  (h: α ↪o β)
  (min_eq: ∀a b: α, h (min a b) = (min (h a) (h b)))
  (max_eq: ∀a b: α, h (max a b) = (max (h a) (h b)))
  : IsLinearLattice α :=
  have := h.instIsPartialOrder'
  {
    h.instIsLinearOrder, h.instIsSemiLatticeMax max_eq, h.instIsSemiLatticeMin min_eq with
  }

end OrderEmbedding

namespace OrderEquiv

def instIsPreOrder {_: LE α} [LT α] {_: LE β} [LT β]
  [IsPreOrder α]
  [IsLawfulLT β]
  (h: α ≃o β): IsPreOrder β :=
  OrderEmbedding.instIsPreOrder (α := β) (β := α) h.symm.toEmbedding

def instIsPartialOrder {_: LE α} [LT α] {_: LE β} [LT β]
  [IsPartialOrder α]
  [_root_.IsPreOrder β]
  (h: α ≃o β): IsPartialOrder β :=
  OrderEmbedding.instIsPartialOrder (α := β) (β := α) h.symm.toEmbedding

def instIsPartialOrder' {_: LE α} [LT α] {_: LE β} [LT β]
  [_root_.IsPartialOrder α]
  [IsLawfulLT β]
  (h: α ≃o β): _root_.IsPartialOrder β :=
  OrderEmbedding.instIsPartialOrder' (α := β) (β := α) h.symm.toEmbedding

def instIsLinearOrder {_: LE α} [LT α] {_: LE β} [LT β]
  [_root_.IsLinearOrder β]
  [IsLawfulLT α]
  (h: α ≃o β)
  : _root_.IsLinearOrder α := h.toEmbedding.instIsLinearOrder

def instIsSemilatticeMax {_: LE α} [LT α] {_: LE β} [LT β]
  [Max α] [Max β]
  [IsSemiLatticeMax β]
  [IsLawfulLT α]
  (h: α ≃o β)
  (max_eq: ∀a b: α, max a b = h.symm (max (h a) (h b))) :
  IsSemiLatticeMax α :=
  have := h.symm.instIsPartialOrder'
  h.toEmbedding.instIsSemiLatticeMax <| by
    intro a b
    rw [max_eq]; show h (h.symm _) = _
    rw [h.symm_coe]; rfl

def instIsSemilatticeMin {_: LE α} [LT α] {_: LE β} [LT β]
  [Min α] [Min β]
  [IsSemiLatticeMin β]
  [IsLawfulLT α]
  (h: α ≃o β)
  (min_eq: ∀a b: α, min a b = h.symm (min (h a) (h b))) :
  IsSemiLatticeMin α :=
  have := h.symm.instIsPartialOrder'
  h.toEmbedding.instIsSemiLatticeMin <| by
    intro a b
    rw [min_eq]; show h (h.symm _) = _
    rw [h.symm_coe]; rfl

def instIsLinearLattice {_: LE α} [LT α] {_: LE β} [LT β]
  [Min α] [Min β] [Max α] [Max β]
  [IsLinearLattice β]
  [IsLawfulLT α]
  (h: α ≃o β)
  (min_eq: ∀a b: α, min a b = h.symm (min (h a) (h b)))
  (max_eq: ∀a b: α, max a b = h.symm (max (h a) (h b)))
  : IsLinearLattice α :=
  {
    h.instIsLinearOrder, h.instIsSemilatticeMax max_eq, h.instIsSemilatticeMin min_eq with
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
    toIsLinearLattice := h.instIsLinearLattice min_eq max_eq
    min_def := by
      intro a b
      rw [min_eq, min_def]
      split
      rw [←(map_le h)] at *
      rw [if_pos, h.coe_symm]; assumption
      rw [←(map_le h)] at *
      rw [if_neg, h.coe_symm]; assumption
    max_def := by
      intro a b
      rw [max_eq, max_def]
      split
      rw [←(map_le h)] at *
      rw [if_pos, h.coe_symm]; assumption
      rw [←(map_le h)] at *
      rw [if_neg, h.coe_symm]; assumption
    decLE a b := decidable_of_iff (h a ≤ h b) (map_le h).symm
  }

def instMin [Min β] (h: α ≃o β) : Min α where
  min a b := h.symm (min (h a) (h b))
def instMax [Max β] (h: α ≃o β) : Max α where
  max a b := h.symm (max (h a) (h b))

end OrderEquiv

namespace Opposite

def orderIsoCongr {_: LE α} {_: LE β} (h: α ≃o β) : Opposite α ≃o Opposite β where
  toFun := h
  invFun := h.symm
  leftInv := h.leftInv
  rightInv := h.rightInv
  map_le _ _ := h.map_le _ _

def orderEmbeddingCongr {_: LE α} {_: LE β} (h: α ↪o β) : Opposite α ↪o Opposite β where
  toFun := h
  inj' := h.inj
  map_le _ _ := h.map_le _ _

end Opposite

instance [LE β] : LE (α ↪ β) where
  le f g := f.toFun ≤ g.toFun

instance [LE β] : LT (α ↪ β) where
  lt f g := f.toFun < g.toFun

instance [LE β] : LE (α ↪o β) where
  le f g := f.toFun ≤ g.toFun

instance [LE β] : LT (α ↪o β) where
  lt f g := f.toFun < g.toFun

instance [LE β] : LE (α →o β) where
  le f g := f.toFun ≤ g.toFun

instance [LE β] : LT (α →o β) where
  lt f g := f.toFun < g.toFun

instance [LE β] : LE (α →≤ β) where
  le f g := f.toFun ≤ g.toFun

instance [LE β] : LT (α →≤ β) where
  lt f g := f.toFun < g.toFun

instance [LE β] : LE (α →< β) where
  le f g := f.toFun ≤ g.toFun

instance [LE β] : LT (α →< β) where
  lt f g := f.toFun < g.toFun

instance : IsLawfulLT (α ↪ β) where
  lt_iff_le_and_not_le := Iff.rfl
instance : IsLawfulLT (α ↪o β) where
  lt_iff_le_and_not_le := Iff.rfl
instance : IsLawfulLT (α →o β) where
  lt_iff_le_and_not_le := Iff.rfl
instance : IsLawfulLT (α →≤ β) where
  lt_iff_le_and_not_le := Iff.rfl
instance : IsLawfulLT (α →< β) where
  lt_iff_le_and_not_le := Iff.rfl

def Embedding.oemb_fun : (α ↪ β) ↪o (α -> β) where
  toFun f := f
  inj' :=  by intro ⟨x, _⟩ ⟨y, _⟩ eq; congr
  map_le _ _ := Iff.rfl

instance [IsPreOrder β] : IsPreOrder (α ↪ β) :=
  Embedding.oemb_fun.instIsPreOrder

instance [IsPartialOrder β] : IsPartialOrder (α ↪ β) :=
  Embedding.oemb_fun.instIsPartialOrder

def MonotoneHom.oemb_fun : (α →≤ β) ↪o (α -> β) where
  toFun f := f
  inj' :=  by intro ⟨x, _⟩ ⟨y, _⟩ eq; congr
  map_le _ _ := Iff.rfl

instance [IsPreOrder β] : IsPreOrder (α →≤ β) :=
  MonotoneHom.oemb_fun.instIsPreOrder

instance [IsPartialOrder β] : IsPartialOrder (α →≤ β) :=
  MonotoneHom.oemb_fun.instIsPartialOrder

def StrictMonotoneHom.oemb_fun : (α →< β) ↪o (α -> β) where
  toFun f := f
  inj' :=  by intro ⟨x, _⟩ ⟨y, _⟩ eq; congr
  map_le _ _ := Iff.rfl

instance [IsPreOrder β] : IsPreOrder (α →< β) :=
  StrictMonotoneHom.oemb_fun.instIsPreOrder

instance [IsPartialOrder β] : IsPartialOrder (α →< β) :=
  StrictMonotoneHom.oemb_fun.instIsPartialOrder

def OrderHom.oemb_fun : (α →o β) ↪o (α -> β) where
  toFun f := f
  inj' :=  by intro ⟨x, _⟩ ⟨y, _⟩ eq; congr
  map_le _ _ := Iff.rfl

instance [IsPreOrder β] : IsPreOrder (α →o β) :=
  OrderHom.oemb_fun.instIsPreOrder

instance [IsPartialOrder β] : IsPartialOrder (α →o β) :=
  OrderHom.oemb_fun.instIsPartialOrder

def OrderEmbedding.oemb_fun : (α ↪o β) ↪o (α ↪ β) where
  toFun f := f
  inj' :=  by intro ⟨x, _⟩ ⟨y, _⟩ eq; congr
  map_le _ _ := Iff.rfl

instance [IsPreOrder β] : IsPreOrder (α ↪o β) :=
  OrderEmbedding.oemb_fun.instIsPreOrder

instance [IsPartialOrder β] : IsPartialOrder (α ↪o β) :=
  OrderEmbedding.oemb_fun.instIsPartialOrder

def OrderEmbedding.toLtRelEmbedding
  [IsPreOrder α] [IsPreOrder β]
  (h: α ↪o β) : @RelEmbedding α β (· < ·) (· < ·) where
  toFun := h
  inj' := h.inj
  resp_rel := by
    intro x y; dsimp
    rw [lt_iff_le_and_not_le, lt_iff_le_and_not_le, (map_le h), (map_le h)]
