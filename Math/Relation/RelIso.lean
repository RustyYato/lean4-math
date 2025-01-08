import Math.Type.Basic
import Math.Relation.Basic

section

variable {α β γ: Type*} (r: α -> α -> Prop) (s: β -> β -> Prop)

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

variable {r: α -> α -> Prop} {s: β -> β -> Prop} {t: γ -> γ -> Prop}

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

namespace RelHom

def acc (f : r →r s) (a : α) : Acc s (f a) → Acc r a := by
  generalize fa_def:f a = fa
  intro acc
  induction acc generalizing a with
  | intro acc h ih =>
  subst acc
  apply Acc.intro
  intro b rba
  apply ih
  apply f.resp_rel
  assumption
  rfl

def wf (h: r →r s) [Relation.IsWellFounded s] : Relation.IsWellFounded r where
  wf := ⟨fun x => h.acc x (Relation.acc s (h x))⟩

def irrefl (h: s →r r) [Relation.IsIrrefl r] : Relation.IsIrrefl s where
  irrefl rel := Relation.irrefl (h.resp_rel rel)

end RelHom

namespace RelEmbedding

def refl : r ↪r r where
  toEmbedding := .refl
  resp_rel := Iff.rfl

def trans (h: r ↪r s) (g: s ↪r t) : r ↪r t where
  toEmbedding := Embedding.trans h.toEmbedding g.toEmbedding
  resp_rel := Iff.trans h.resp_rel g.resp_rel

def wo (h: s ↪r r) [Relation.IsWellOrder r] : Relation.IsWellOrder s where
  toIsWellFounded := h.toRelHom.wf
  trans := by
    intro a b c ab bc
    exact h.resp_rel.mpr <| Relation.trans (h.resp_rel.mp ab) (h.resp_rel.mp bc)
  tri := by
    intro a b
    rcases Relation.trichotomous r (h a) (h b) with ab | eq | ba
    left; exact h.resp_rel.mpr ab
    right; left; exact h.inj eq
    right; right; exact h.resp_rel.mpr ba

end RelEmbedding

namespace RelIso

def inv_resp_rel (h: r ≃r s) : _root_.resp_rel s r h.invFun := by
  intro a b
  rw [←h.rightInv a, ←h.rightInv b, h.leftInv, h.leftInv]
  exact h.resp_rel.symm

@[refl]
def refl : rel ≃r rel where
  toEquiv := .refl
  resp_rel := Iff.refl _

@[symm]
def symm (h: r ≃r s) : s ≃r r where
  toEquiv := h.toEquiv.symm
  resp_rel := h.inv_resp_rel

def trans (h: r ≃r s) (g: s ≃r t) : r ≃r t where
  toEquiv := .trans h.toEquiv g.toEquiv
  resp_rel := Iff.trans h.resp_rel g.resp_rel

def coe_symm (h: r ≃r s) (x: α) : h.symm (h x) = x := h.leftInv _
def symm_coe (h: r ≃r s) (x: β) : h (h.symm x) = x := h.rightInv _

end RelIso

namespace RelIso

def wf (h: s ≃r r) [Relation.IsWellFounded r] : Relation.IsWellFounded s :=
  h.toRelHom.wf

def irrefl (h: s ≃r r) [Relation.IsIrrefl r] : Relation.IsIrrefl s :=
  h.toRelHom.irrefl

def tri (h: s ≃r r) [Relation.IsTrichotomous s] : Relation.IsTrichotomous r where
  tri a b := by
    rcases Relation.trichotomous s (h.symm a) (h.symm b) with ab | eq | ba
    exact .inl <| h.inv_resp_rel.mpr ab
    exact .inr <| .inl <| h.invFun_inj eq
    exact .inr <| .inr <| h.inv_resp_rel.mpr ba

def trans' (h: s ≃r r) [Relation.IsTrans s] : Relation.IsTrans r where
  trans := by
    intro a b c ab bc
    apply h.inv_resp_rel.mpr
    apply Relation.trans
    exact h.inv_resp_rel.mp ab
    exact h.inv_resp_rel.mp bc

end RelIso

def RelEmbedding.congr (eqr: r₀ ≃r r₁) (eqs: s₀ ≃r s₁) (h: r₀ ↪r s₀) : r₁ ↪r s₁ where
  toEmbedding := h.toEmbedding.congr eqr.toEquiv eqs.toEquiv
  resp_rel := by
    intro a b
    unfold Embedding.congr
    dsimp
    apply Iff.trans _ eqs.resp_rel
    apply Iff.trans _ h.resp_rel
    exact eqr.symm.resp_rel

def RelEmbedding.congr_apply (emb: r₀ ↪r s₀) (eqa: r₀ ≃r r₁) (eqb: s₀ ≃r s₁): (emb.congr eqa eqb) x = eqb (emb (eqa.symm x)) := rfl

end
