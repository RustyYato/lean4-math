import Math.Relation.RelIso
import Math.Order.Partial

variable {α β: Type*} [LE α] [LT α] [LE β] [LT β]

def OrderEmbedding (α β: Type*) [LE α] [LE β] :=
  @RelEmbedding α β (· ≤ ·) (· ≤ ·)

def OrderIso (α β: Type*) [LE α] [LE β] :=
  @RelIso α β (· ≤ ·) (· ≤ ·)
infixl:25 " ↪o " => OrderEmbedding
infixl:25 " ≃o " => OrderIso

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

instance : FunLike (α ↪o β) α β where
  coe e := e.toFun
  coe_inj := by
    intro ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ eq
    congr

instance : IsEmbeddingLike (α ↪o β) α β where
  coe_inj e := e.inj

instance : IsEquivLike (α ≃o β) α β where
  coe e := e.toFun
  inv e := e.invFun
  leftInv e := e.leftInv
  rightInv e := e.rightInv
  inj := by
    intro ⟨⟨_, _, _, _⟩, _⟩ ⟨⟨_, _, _, _⟩, _⟩ _ _
    congr

def coe_symm (h: α ≃o β) (x: α) : h.symm (h x) = x := h.leftInv _
def symm_coe (h: α ≃o β) (x: β) : h (h.symm x) = x := h.rightInv _

def resp_le {_: LE α} {_: LE β} (h: α ≃o β) : ∀{a b: α}, a ≤ b ↔ h a ≤ h b := h.resp_rel
def symm_resp_le {_: LE α} {_: LE β} (h: α ≃o β) : ∀{a b: β}, a ≤ b ↔ h.symm a ≤ h.symm b := h.symm.resp_rel

def instIsPreOrder {_: LE α} [LT α] {_: LE β} [LT β]
  [IsPreOrder α]
  (h: α ≃o β)
  (resp_lt: ∀{a b: α}, a < b ↔ h a < h b)
  : IsPreOrder β where
  lt_iff_le_and_not_le := by
    intro a b
    suffices ∀{a b: β}, a < b ↔ h.symm a < h.symm b by
      rw [this, h.symm.resp_le, h.symm.resp_le]
      exact lt_iff_le_and_not_le
    intro a b
    rw [←h.symm_coe a, ←h.symm_coe b, h.coe_symm, h.coe_symm, ←resp_lt]
  le_refl _ := h.symm.resp_le.mpr (le_refl _)
  le_trans := by
    intro a b c
    iterate 3 rw [h.symm.resp_le]
    exact le_trans

def instIsPartialOrder {_: LE α} [LT α] {_: LE β} [LT β]
  [IsPartialOrder α]
  [_root_.IsPreOrder β]
  (h: α ≃o β)
  : IsPartialOrder β where
  le_antisymm := by
    intro a b
    iterate 2 rw [h.symm.resp_le]
    intro ab ba
    have := le_antisymm ab ba
    exact h.invFun_inj this

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
