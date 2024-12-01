import Math.Type.Basic

section

variable {α β: Type*} (r: α -> α -> Prop) (s: β -> β -> Prop)

abbrev resp_rel (toFun: α -> β) := ∀{a b: α}, r a b ↔ s (toFun a) (toFun b)

structure RelHom where
  toFun: α -> β
  resp_rel: ∀{a b: α}, r a b -> s (toFun a) (toFun b)

class IsRelHom
  (F: Type*) {α β: Type*}
  (r: outParam <| α -> α -> Prop) (s: outParam <| β -> β -> Prop)
  [FunLike F α β]: Prop where
  resp_rel (f: F): ∀a b, r a b -> s (f a) (f b)

infixl:25 " →r " => RelHom

structure RelEmbedding extends α ↪ β where
  resp_rel: resp_rel r s toFun

infixr:25 " ↪r " => RelEmbedding

structure RelIso extends α ≃ β where
  resp_rel: resp_rel r s toFun

infixl:25 " ≃r " => RelIso

variable {r: α -> α -> Prop} {s: β -> β -> Prop}

def RelEmbedding.toRelHom (h: r ↪r s) : r →r s where
  toFun := h.toFun
  resp_rel := h.resp_rel.mp

def RelIso.toRelEmbedding (h: r ≃r s) : r ↪r s where
  toFun := h.toFun
  resp_rel := h.resp_rel
  inj := h.toEquiv.toFun_inj

def RelIso.toRelHom (h: r ≃r s) : r →r s := h.toRelEmbedding.toRelHom

def RelEmbedding.toRelHom_inj : Function.Injective (toRelHom (r := r) (s := s)) := by
  intro x y h
  cases x; cases y; rename_i x _ y _
  cases x with | mk xab inj =>
  cases y with | mk yab inj =>
  congr
  unfold toRelHom at h
  dsimp at h
  exact RelHom.mk.inj h

def RelIso.toRelEmbedding_inj : Function.Injective (toRelEmbedding (r := r) (s := s)) := by
  intro x y h
  cases x; cases y; rename_i x _ y _
  cases x with | mk xab xba xlinv xrinv =>
  cases y with | mk yab yba ylinv yrinv =>
  unfold toRelEmbedding at h
  dsimp at h
  have := Embedding.mk.inj (RelEmbedding.mk.inj h)
  congr
  subst yab
  exact Function.inverse_congr xlinv yrinv

def RelIso.toRelHom_inj : Function.Injective (toRelHom (r := r) (s := s)) := by
  apply Function.Injective.comp
  apply RelEmbedding.toRelHom_inj
  apply RelIso.toRelEmbedding_inj

instance : FunLike (r →r s) α β where
  coe h := h.toFun
  coe_inj x y := by
    intro h
    cases x; cases y; rename_i x _ y _
    dsimp at h
    congr

instance : FunLike (r ↪r s) α β := by
  apply FunLike.comp RelEmbedding.toRelHom
  apply RelEmbedding.toRelHom_inj

instance : FunLike (r ≃r s) α β := by
  apply FunLike.comp RelIso.toRelHom
  apply RelIso.toRelHom_inj

instance : IsRelHom (r →r s) r s where
  resp_rel := RelHom.resp_rel

instance : IsRelHom (r ↪r s) r s where
  resp_rel h _ _ := h.resp_rel.mp

instance : IsRelHom (r ≃r s) r s where
  resp_rel h _ _ := h.resp_rel.mp

end
