import Math.Relation.RelIso
import Math.Logic.Equiv.Like
import Math.Order.Defs

variable {α β: Type*} [LE α] [LT α] [LE β] [LT β]

def OrderHom (α β: Type*) [LE α] [LE β] :=
  @RelHom α β (· ≤ ·) (· ≤ ·)

def OrderEmbedding (α β: Type*) [LE α] [LE β] :=
  @RelEmbedding α β (· ≤ ·) (· ≤ ·)

def OrderIso (α β: Type*) [LE α] [LE β] :=
  @RelIso α β (· ≤ ·) (· ≤ ·)

infixl:25 " →o " => OrderHom
infixl:25 " ↪o " => OrderEmbedding
infixl:25 " ≃o " => OrderIso

namespace OrderEmbedding

instance : FunLike (α ↪o β) α β where
  coe e := e.toFun
  coe_inj := by
    intro ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ eq
    congr

instance : EmbeddingLike (α ↪o β) α β where
  coe e := e.toEmbedding
  coe_inj := by intro a b eq; cases a; cases b; congr

@[refl]
def refl [LE α] : α ↪o α where
  toEmbedding := .rfl
  resp_rel := Iff.rfl

def trans {_: LE α} {_: LE β} {_: LE γ} (h: α ↪o β) (g: β ↪o γ) : α ↪o γ where
  toEmbedding := .trans h.toEmbedding g.toEmbedding
  resp_rel := h.resp_rel.trans g.resp_rel

def resp_le {_: LE α} {_: LE β} (h: α ↪o β) : ∀{a b: α}, a ≤ b ↔ h a ≤ h b := h.resp_rel

def resp_lt {_: LE α} {_: LE β} {_: LT α} {_: LT β} [IsLawfulLT α] [IsLawfulLT β] (h: α ↪o β) : ∀{a b: α}, a < b ↔ h a < h b := by
  intro a b
  rw [lt_iff_le_and_not_le, lt_iff_le_and_not_le, h.resp_le, h.resp_le]

def inj (h: α ↪o β) : Function.Injective h := Embedding.inj h.toEmbedding

def inducedIsPreOrder {_: LE α} [LT α] {_: LE β} [LT β]
  [IsPreOrder β]
  [IsLawfulLT α]
  (h: α ↪o β)
  : IsPreOrder α where
  le_refl _ := h.resp_le.mpr (le_refl _)
  le_trans := by
    intro a b c
    iterate 3 rw [h.resp_le]
    exact le_trans

def inducedIsPartialOrder {_: LE α} [LT α] {_: LE β} [LT β]
  [IsPartialOrder β]
  [_root_.IsPreOrder α]
  (h: α ↪o β)
  : IsPartialOrder α where
  le_antisymm := by
    intro a b
    iterate 2 rw [h.resp_le]
    intro ab ba
    have := le_antisymm ab ba
    exact h.inj this

def inducedIsPartialOrder' {_: LE α} [LT α] {_: LE β} [LT β]
  [_root_.IsPartialOrder β]
  [IsLawfulLT α]
  (h: α ↪o β)
  : _root_.IsPartialOrder α where
  toIsPreOrder := h.inducedIsPreOrder
  le_antisymm := by
    intro a b
    rw [h.resp_le, h.resp_le]
    intro ab ba
    exact h.inj (le_antisymm ab ba)

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

def instIsLawfulTop {_: LE α} [LT α] {_: LE β} [LT β]
  [Top α] [Top β]
  [IsLawfulTop β]
  (h: α ↪o β) (map_top: h ⊤ = ⊤) : IsLawfulTop α where
  le_top := by
    intro x
    apply h.resp_le.mpr
    rw [map_top]
    apply le_top

def instIsLawfulBot {_: LE α} [LT α] {_: LE β} [LT β]
  [Bot α] [Bot β]
  [IsLawfulBot β]
  (h: α ↪o β) (map_bot: h ⊥ = ⊥) : IsLawfulBot α where
  bot_le := by
    intro x
    apply h.resp_le.mpr
    rw [map_bot]
    apply bot_le

end OrderEmbedding

namespace OrderIso

@[refl]
def refl [LE α] : α ≃o α where
  toEquiv := .rfl
  resp_rel := Iff.rfl

@[symm]
def symm {_: LE α} {_: LE β} (h: α ≃o β) : β ≃o α where
  toEquiv := .symm h.toEquiv
  resp_rel := h.inv_resp_rel

def trans {_: LE α} {_: LE β} {_: LE γ} (h: α ≃o β) (g: β ≃o γ) : α ≃o γ where
  toEquiv := .trans h.toEquiv g.toEquiv
  resp_rel := h.resp_rel.trans g.resp_rel

instance : Coe (α ≃o β) (α ↪o β) where
  coe h := {
    toEmbedding := h.toEmbedding
    resp_rel := h.resp_rel
  }

def toEmbedding (h: α ≃o β) : α ↪o β := h

instance : EquivLike (α ≃o β) α β where
  coe e := e.toEquiv
  coe_inj := by intro a b eq; cases a; cases b; congr

instance : FunLike (α →o β) α β where
  coe e := e.toFun
  coe_inj := by
    intro ⟨_, _⟩ ⟨_, _⟩ eq
    congr

def coe_symm (h: α ≃o β) (x: α) : h.symm (h x) = x := h.leftInv _
def symm_coe (h: α ≃o β) (x: β) : h (h.symm x) = x := h.rightInv _

def resp_le {_: LE α} {_: LE β} (h: α ≃o β) : ∀{a b: α}, a ≤ b ↔ h a ≤ h b := h.resp_rel
def symm_resp_le {_: LE α} {_: LE β} (h: α ≃o β) : ∀{a b: β}, a ≤ b ↔ h.symm a ≤ h.symm b := h.symm.resp_rel

def resp_lt {_: LE α} {_: LE β} {_: LT α} {_: LT β} [IsLawfulLT α] [IsLawfulLT β] (h: α ≃o β) : ∀{a b: α}, a < b ↔ h a < h b := by
  intro a b
  rw [lt_iff_le_and_not_le, lt_iff_le_and_not_le, h.resp_le, h.resp_le]

def inj (h: α ≃o β) : Function.Injective h := Equiv.inj h.toEquiv

def instIsPreOrder {_: LE α} [LT α] {_: LE β} [LT β]
  [IsPreOrder α]
  [IsLawfulLT β]
  (h: α ≃o β): IsPreOrder β :=
  OrderEmbedding.inducedIsPreOrder (α := β) (β := α) h.symm

def instIsPartialOrder {_: LE α} [LT α] {_: LE β} [LT β]
  [IsPartialOrder α]
  [_root_.IsPreOrder β]
  (h: α ≃o β): IsPartialOrder β :=
  OrderEmbedding.inducedIsPartialOrder (α := β) (β := α) h.symm

def instIsPartialOrder' {_: LE α} [LT α] {_: LE β} [LT β]
  [_root_.IsPartialOrder α]
  [IsLawfulLT β]
  (h: α ≃o β): _root_.IsPartialOrder β :=
  OrderEmbedding.inducedIsPartialOrder' (α := β) (β := α) h.symm

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

def instMin [Min β] (h: α ≃o β) : Min α where
  min a b := h.symm (min (h a) (h b))
def instMax [Max β] (h: α ≃o β) : Max α where
  max a b := h.symm (max (h a) (h b))

end OrderIso

namespace Opposite

def orderIsoCongr {_: LE α} {_: LE β} (h: α ≃o β) : Opposite α ≃o Opposite β where
  toFun := h
  invFun := h.symm
  leftInv := h.leftInv
  rightInv := h.rightInv
  resp_rel := h.resp_rel

def orderEmbeddingCongr {_: LE α} {_: LE β} (h: α ↪o β) : Opposite α ↪o Opposite β where
  toFun := h
  inj' := h.inj
  resp_rel := h.resp_rel

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

def Embedding.oemb_fun : (α ↪ β) ↪o (α -> β) where
  toFun := Embedding.toFun
  inj' :=  by intro ⟨x, _⟩ ⟨y, _⟩ eq; congr
  resp_rel := Iff.rfl

instance : IsLawfulLT (α ↪ β) where
  lt_iff_le_and_not_le := Iff.rfl
instance : IsLawfulLT (α ↪o β) where
  lt_iff_le_and_not_le := Iff.rfl
instance : IsLawfulLT (α →o β) where
  lt_iff_le_and_not_le := Iff.rfl

instance [IsPreOrder β] : IsPreOrder (α ↪ β) :=
  Embedding.oemb_fun.inducedIsPreOrder

instance [IsPartialOrder β] : IsPartialOrder (α ↪ β) :=
  Embedding.oemb_fun.inducedIsPartialOrder

def OrderHom.oemb_fun : (α →o β) ↪o (α -> β) where
  toFun := RelHom.toFun
  inj' :=  by intro ⟨x, _⟩ ⟨y, _⟩ eq; congr
  resp_rel := Iff.rfl

instance [IsPreOrder β] : IsPreOrder (α →o β) :=
  OrderHom.oemb_fun.inducedIsPreOrder

instance [IsPartialOrder β] : IsPartialOrder (α →o β) :=
  OrderHom.oemb_fun.inducedIsPartialOrder

def OrderEmbedding.oemb_fun : (α ↪o β) ↪o (α ↪ β) where
  toFun := RelEmbedding.toEmbedding
  inj' :=  by intro ⟨x, _⟩ ⟨y, _⟩ eq; congr
  resp_rel := Iff.rfl

instance [IsPreOrder β] : IsPreOrder (α ↪o β) :=
  OrderEmbedding.oemb_fun.inducedIsPreOrder

instance [IsPartialOrder β] : IsPartialOrder (α ↪o β) :=
  OrderEmbedding.oemb_fun.inducedIsPartialOrder

def OrderEmbedding.toLtRelEmbedding
  [IsPreOrder α] [IsPreOrder β]
  (h: α ↪o β) : @RelEmbedding α β (· < ·) (· < ·) where
  toFun := h
  inj' := h.inj
  resp_rel := by
    intro x y; dsimp
    rw [lt_iff_le_and_not_le, lt_iff_le_and_not_le, h.resp_le, h.resp_le]
