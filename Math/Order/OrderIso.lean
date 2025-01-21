import Math.Relation.RelIso
import Math.Order.Partial

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

instance : IsEmbeddingLike (α ↪o β) α β where
  coe_inj e := e.inj

@[refl]
def refl [LE α] : α ↪o α where
  toEmbedding := .refl
  resp_rel := Iff.rfl

def trans {_: LE α} {_: LE β} {_: LE γ} (h: α ↪o β) (g: β ↪o γ) : α ↪o γ where
  toEmbedding := .trans h.toEmbedding g.toEmbedding
  resp_rel := h.resp_rel.trans g.resp_rel

def resp_le {_: LE α} {_: LE β} (h: α ↪o β) : ∀{a b: α}, a ≤ b ↔ h a ≤ h b := h.resp_rel

def inducedIsPreOrder {_: LE α} [LT α] {_: LE β} [LT β]
  [IsPreOrder β]
  (h: α ↪o β)
  (resp_lt: ∀{a b: α}, a < b ↔ h a < h b)
  : IsPreOrder α where
  lt_iff_le_and_not_le := by
    intro a b
    rw [resp_lt, h.resp_le, h.resp_le]
    apply lt_iff_le_and_not_le
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
  (h: α ↪o β)
  (resp_lt: ∀{a b: α}, a < b ↔ h a < h b)
  : _root_.IsPartialOrder α where
  toIsPreOrder := h.inducedIsPreOrder resp_lt
  le_antisymm :=
    have := h.inducedIsPreOrder resp_lt
    h.inducedIsPartialOrder.le_antisymm

end OrderEmbedding

namespace OrderIso

@[refl]
def refl [LE α] : α ≃o α where
  toEquiv := .refl
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

instance : IsEquivLike (α ≃o β) α β where
  coe e := e.toFun
  inv e := e.invFun
  leftInv e := e.leftInv
  rightInv e := e.rightInv
  inj := by
    intro ⟨⟨_, _, _, _⟩, _⟩ ⟨⟨_, _, _, _⟩, _⟩ _ _
    congr

instance : FunLike (α →o β) α β where
  coe e := e.toFun
  coe_inj := by
    intro ⟨_, _⟩ ⟨_, _⟩ eq
    congr

def coe_symm (h: α ≃o β) (x: α) : h.symm (h x) = x := h.leftInv _
def symm_coe (h: α ≃o β) (x: β) : h (h.symm x) = x := h.rightInv _

def resp_le {_: LE α} {_: LE β} (h: α ≃o β) : ∀{a b: α}, a ≤ b ↔ h a ≤ h b := h.resp_rel
def symm_resp_le {_: LE α} {_: LE β} (h: α ≃o β) : ∀{a b: β}, a ≤ b ↔ h.symm a ≤ h.symm b := h.symm.resp_rel

def instIsPreOrder {_: LE α} [LT α] {_: LE β} [LT β]
  [IsPreOrder α]
  (h: α ≃o β)
  (resp_lt: ∀{a b: α}, a < b ↔ h a < h b)
  : IsPreOrder β := OrderEmbedding.inducedIsPreOrder (α := β) (β := α) h.symm <| by
    intro a b
    show a < b ↔ h.symm a < h.symm b
    conv => { lhs; rw [←h.symm_coe a, ←h.symm_coe b] }
    apply resp_lt.symm

def instIsPartialOrder {_: LE α} [LT α] {_: LE β} [LT β]
  [IsPartialOrder α]
  [_root_.IsPreOrder β]
  (h: α ≃o β)
  : IsPartialOrder β := OrderEmbedding.inducedIsPartialOrder (α := β) (β := α) h.symm

def instIsPartialOrder' {_: LE α} [LT α] {_: LE β} [LT β]
  [_root_.IsPartialOrder α]
  (h: α ≃o β)
  (resp_lt: ∀{a b: α}, a < b ↔ h a < h b)
  : _root_.IsPartialOrder β where
  toIsPreOrder := h.instIsPreOrder resp_lt
  le_antisymm :=
    have := h.instIsPreOrder resp_lt
    h.instIsPartialOrder.le_antisymm

end OrderIso

namespace OrderDual

def orderIsoCongr {_: LE α} {_: LE β} (h: α ≃o β) : OrderDual α ≃o OrderDual β where
  toFun := h
  invFun := h.symm
  leftInv := h.leftInv
  rightInv := h.rightInv
  resp_rel := h.resp_rel

end OrderDual

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
  inj :=  by intro ⟨x, _⟩ ⟨y, _⟩ eq; congr
  resp_rel := Iff.rfl

instance [IsPreOrder β] : IsPreOrder (α ↪ β) :=
  Embedding.oemb_fun.inducedIsPreOrder Iff.rfl

instance [IsPartialOrder β] : IsPartialOrder (α ↪ β) :=
  Embedding.oemb_fun.inducedIsPartialOrder

def OrderHom.oemb_fun : (α →o β) ↪o (α -> β) where
  toFun := RelHom.toFun
  inj :=  by intro ⟨x, _⟩ ⟨y, _⟩ eq; congr
  resp_rel := Iff.rfl

instance [IsPreOrder β] : IsPreOrder (α →o β) :=
  OrderHom.oemb_fun.inducedIsPreOrder Iff.rfl

instance [IsPartialOrder β] : IsPartialOrder (α →o β) :=
  OrderHom.oemb_fun.inducedIsPartialOrder

def OrderEmbedding.oemb_fun : (α ↪o β) ↪o (α ↪ β) where
  toFun := RelEmbedding.toEmbedding
  inj :=  by intro ⟨x, _⟩ ⟨y, _⟩ eq; congr
  resp_rel := Iff.rfl

instance [IsPreOrder β] : IsPreOrder (α ↪o β) :=
  OrderEmbedding.oemb_fun.inducedIsPreOrder Iff.rfl

instance [IsPartialOrder β] : IsPartialOrder (α ↪o β) :=
  OrderEmbedding.oemb_fun.inducedIsPartialOrder
