import Math.Logic.Equiv.Basic
import Math.Relation.Basic

section

variable {α β γ: Sort*} (r: α -> α -> Prop) (s: β -> β -> Prop)

abbrev resp_rel (toFun: α -> β) := ∀{a b: α}, r a b ↔ s (toFun a) (toFun b)

structure RelHom where
  toFun: α -> β
  resp_rel: ∀{a b: α}, r a b -> s (toFun a) (toFun b)

class IsRelHom
  (F: Sort*) {α β: Sort*}
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
  inj' := h.toEquiv.inj

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

def comp (h: r →r s) (g: s →r t) : r →r t where
  toFun := g ∘ h
  resp_rel := g.resp_rel ∘ h.resp_rel

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
  toEmbedding := .rfl
  resp_rel := Iff.rfl

def trans (h: r ↪r s) (g: s ↪r t) : r ↪r t where
  toEmbedding := Embedding.trans h.toEmbedding g.toEmbedding
  resp_rel := Iff.trans h.resp_rel g.resp_rel

def tri (h: s ↪r r) [Relation.IsTrichotomous r] : Relation.IsTrichotomous s where
  tri := by
    intro a b
    rcases Relation.trichotomous r (h a) (h b) with ab | eq | ba
    left; exact h.resp_rel.mpr ab
    right; left; exact h.inj eq
    right; right; exact h.resp_rel.mpr ba

def wo (h: s ↪r r) [Relation.IsWellOrder r] : Relation.IsWellOrder s where
  toIsWellFounded := h.toRelHom.wf
  toIsTrichotomous := h.tri
  trans := by
    intro a b c ab bc
    exact h.resp_rel.mpr <| Trans.trans (h.resp_rel.mp ab) (h.resp_rel.mp bc)

end RelEmbedding

namespace RelIso

def inv_resp_rel (h: r ≃r s) : _root_.resp_rel s r h.invFun := by
  intro a b
  rw [←h.rightInv a, ←h.rightInv b, h.leftInv, h.leftInv]
  exact h.resp_rel.symm

@[refl]
def refl : rel ≃r rel where
  toEquiv := .rfl
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

def symm_inj : Function.Injective (symm (r := r) (s := s)) := by
  intro ⟨x, _⟩ ⟨y, _⟩ h
  congr
  apply Equiv.equiv_symm.inj
  exact RelIso.mk.inj h

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
    exact .inr <| .inl <| h.symm.inj eq
    exact .inr <| .inr <| h.inv_resp_rel.mpr ba

def trans' (h: s ≃r r) [Relation.IsTrans s] : Relation.IsTrans r where
  trans := by
    intro a b c ab bc
    apply h.inv_resp_rel.mpr
    apply Relation.IsTrans.trans
    exact h.inv_resp_rel.mp ab
    exact h.inv_resp_rel.mp bc

end RelIso

def RelEmbedding.congr (eqr: r₀ ≃r r₁) (eqs: s₀ ≃r s₁) (h: r₀ ↪r s₀) : r₁ ↪r s₁ where
  toEmbedding := Equiv.congrEmbed eqr.toEquiv eqs.toEquiv h.toEmbedding
  resp_rel := by
    intro a b
    apply Iff.trans _ eqs.resp_rel
    apply Iff.trans _ h.resp_rel
    exact eqr.symm.resp_rel

def RelEmbedding.congr_apply (emb: r₀ ↪r s₀) (eqa: r₀ ≃r r₁) (eqb: s₀ ≃r s₁): (emb.congr eqa eqb) x = eqb (emb (eqa.symm x)) := rfl

end

def Fin.relEmbedNat : (· < (·: Fin n)) ↪r (· < (·: Nat)) where
  toEmbedding := Fin.embedNat
  resp_rel := Iff.rfl

def Fin.relEmbedFin (h: n ≤ m) : (· < (·: Fin n)) ↪r (· < (·: Fin m)) where
  toEmbedding := Fin.embedFin h
  resp_rel := Iff.rfl

def Subtype.relEmbed {P: α -> Prop} (r: α -> α -> Prop) : (fun a b: Subtype P => r a b) ↪r r where
  toEmbedding := Embedding.subtypeVal
  resp_rel := Iff.rfl

def ULift.relIso (r: α -> α -> Prop) : (fun a b: ULift α => r a.down b.down) ≃r r where
  toEquiv := (Equiv.ulift _)
  resp_rel := Iff.rfl

def empty_reliso_empty {α β: Sort*} [IsEmpty α] [IsEmpty β] (r: α -> α -> Prop) (s: β -> β -> Prop) : r ≃r s where
  toEquiv := Equiv.empty
  resp_rel {x} := elim_empty x

def Fin.gt_reqv_lt : (· > (·: Fin n)) ≃r (· < (·: Fin n)) where
  toFun := Fin.rev
  invFun := Fin.rev
  leftInv := by
    intro x
    rw [Fin.rev_rev]
  rightInv := by
    intro x
    rw [Fin.rev_rev]
  resp_rel := by
    intro x y
    dsimp
    exact Iff.symm rev_lt_rev

instance : @Relation.IsWellFounded Nat (· < ·) where
  wf := Nat.lt_wfRel.wf

instance : @Relation.IsWellFounded (Fin n) (· < ·) :=
  Fin.relEmbedNat.toRelHom.wf

instance : @Relation.IsWellFounded (Fin n) (· > ·) :=
  Fin.gt_reqv_lt.toRelHom.wf

namespace Relation

def ofMappedTransGen [IsTrans s] (h: TransGen r a b) (g: r →r s) : s (g a) (g b) := by
  induction h with
  | single =>
    apply g.resp_rel
    assumption
  | tail x xs ih =>
    apply trans' ih
    apply g.resp_rel
    assumption

def ofMappedReflTransGen [IsRefl s] [IsTrans s] (h: ReflTransGen r a b) (g: r →r s) : s (g a) (g b) := by
  induction h with
  | refl => rfl
  | cons x xs ih =>
    apply trans' _ ih
    apply g.resp_rel
    assumption

def ofMappedEquivGen [IsRefl s] [IsSymmetric s] [IsTrans s] (h: EquivGen r a b) (g: r →r s) : s (g a) (g b) := by
  induction h with
  | single =>
    apply g.resp_rel
    assumption
  | refl => rfl
  | symm _ _ =>
    apply symm
    assumption
  | trans => apply trans' <;> assumption

def TransGen.RelHom : r →r TransGen r where
  toFun := id
  resp_rel := TransGen.single

def ReflTransGen.RelHom : r →r ReflTransGen r where
  toFun := id
  resp_rel := ReflTransGen.single

def EquivGen.RelHom : r →r EquivGen r where
  toFun := id
  resp_rel := EquivGen.single

def TransGen.congrRelHom (h: r →r s) : TransGen r →r TransGen s where
  toFun := h
  resp_rel := (ofMappedTransGen · (RelHom.comp h TransGen.RelHom))

def ReflTransGen.congrRelHom (h: r →r s) : ReflTransGen r →r ReflTransGen s where
  toFun := h
  resp_rel := (ofMappedReflTransGen · (RelHom.comp h ReflTransGen.RelHom))

def EquivGen.congrRelHom (h: r →r s) : EquivGen r →r EquivGen s where
  toFun := h
  resp_rel := (ofMappedEquivGen · (RelHom.comp h EquivGen.RelHom))

end Relation
