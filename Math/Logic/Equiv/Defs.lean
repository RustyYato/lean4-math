import Math.Type.Notation
import Math.Function.Basic
import Math.Data.Like.Func

structure Embedding (α β: Sort*) where
  toFun: α -> β
  inj': Function.Injective toFun

infixr:25 " ↪ " => Embedding

structure Equiv (α β: Sort*) where
  toFun: α -> β
  invFun: β -> α
  leftInv: invFun.IsLeftInverse toFun
  rightInv: invFun.IsRightInverse toFun

infixl:25 " ≃ " => Equiv

structure Surjection (α β: Sort*) where
  toFun: α -> β
  surj': toFun.Surjective

infixl:25 " ↠ " => Surjection

structure Bijection (α β: Sort*) extends α ↪ β, α ↠ β where

infixl:25 " ⇆ " => Bijection

namespace Embedding

@[refl]
def refl (α: Sort*) : α ↪ α where
  toFun := id
  inj' := fun _ _ => id

protected def rfl {α: Sort*} : α ↪ α := .refl _

def trans {α β γ: Sort*} (h: α ↪ β) (g: β ↪ γ) : α ↪ γ where
  toFun := g.toFun ∘ h.toFun
  inj' := Function.Injective.comp g.inj' h.inj'

abbrev comp {α β γ: Sort*} (h: β ↪ γ) (g: α ↪ β) : α ↪ γ := g.trans h

instance : FunLike (Embedding α β) α β where
  coe := toFun
  coe_inj := by
    intro a b eq
    cases a; cases b; congr

@[simp] def toFun_eq_coe (h: α ↪ β) : h.toFun x = h x := rfl

def inj (h: α ↪ b) : Function.Injective h := h.inj'

@[ext]
def ext (a b: α ↪ β) : (∀x, a x = b x) -> a = b := DFunLike.ext _ _

@[simp]
def mk_apply (f: α -> β) (h: Function.Injective f) (x: α) : Embedding.mk f h x = f x := by rfl

protected def Subsingleton [Subsingleton β] (f: α ↪ β) : Subsingleton α where
  allEq a b := by
    apply f.inj
    apply Subsingleton.allEq

protected def DecidableEq (emb: α ↪ β) [DecidableEq β] : DecidableEq α :=
  fun a b =>
  match inferInstanceAs (Decidable (emb a = emb b)) with
  | .isTrue h => .isTrue (emb.inj h)
  | .isFalse h => .isFalse fun g => h (g ▸ rfl)

def copy (f: α ↪ β) (g: α -> β) (h: f = g) : α ↪ β where
  toFun := g
  inj' := h ▸ f.inj

@[simp] def apply_trans (f: α ↪ β) (g: β ↪ γ) (x: α) : f.trans g x = g (f x) := rfl

def congr {f g: α ↪ β} (h: f = g) : ∀x, f x = g x := fun _ => h ▸ rfl

def trans_assoc {h₀: α₀ ↪ α₁} {h₁: α₁ ↪ α₂} {h₂: α₂ ↪ α₃} :
  (h₀.trans h₁).trans h₂ = h₀.trans (h₁.trans h₂) := by rfl

@[simp] def rfl_trans {h₀: α₀ ↪ α₁} : Embedding.rfl.trans h₀ = h₀ := by rfl
@[simp] def trans_rfl {h₀: α₀ ↪ α₁} : h₀.trans Embedding.rfl = h₀ := by rfl

end Embedding

namespace Surjection

instance : FunLike (α ↠ β) α β where

protected def refl (α: Type*) : α ↠ α where
  toFun := id
  surj' _ := ⟨_, rfl⟩

@[refl]
protected def rfl : α ↠ α := .refl _

def trans (f: α ↠ β) (g: β ↠ γ) : α ↠ γ where
  toFun := g ∘ f
  surj' := Function.Surjective.comp g.surj' f.surj'

def surj (f: α ↠ β) : Function.Surjective f := f.surj'

end Surjection

namespace Bijection

instance : FunLike (α ⇆ β) α β where

protected def refl (α: Type*) : α ⇆ α := {
  Embedding.refl _, Surjection.refl _ with
}

@[refl]
protected def rfl : α ⇆ α := .refl _

def trans (f: α ⇆ β) (g: β ⇆ γ) : α ⇆ γ where
  toFun := g ∘ f
  surj' := Function.Surjective.comp g.surj' f.surj'
  inj' := Function.Injective.comp g.inj' f.inj'

def inj (f: α ⇆ β) : Function.Injective f := f.inj'
def surj (f: α ⇆ β) : Function.Surjective f := f.surj'
def bij (f: α ⇆ β) : Function.Bijective f := ⟨f.inj, f.surj⟩

end Bijection

namespace Equiv

@[refl]
def refl (α: Sort*) : α ≃ α where
  toFun := id
  invFun := id
  leftInv _ := rfl
  rightInv _ := rfl

protected def rfl {α: Sort*} : α ≃ α := .refl _

@[symm]
def symm {α β: Sort*} (h: α ≃ β) : β ≃ α where
  toFun := h.invFun
  invFun := h.toFun
  rightInv := h.leftInv
  leftInv := h.rightInv

def trans {α β γ: Sort*} (h: α ≃ β) (g: β ≃ γ) : α ≃ γ where
  toFun := g.toFun ∘ h.toFun
  invFun := h.invFun ∘ g.invFun
  rightInv x := by
    dsimp; rw [h.rightInv, g.rightInv]
  leftInv x := by
    dsimp; rw [g.leftInv, h.leftInv]

abbrev comp {α β γ: Sort*} (h: β ≃ γ) (g: α ≃ β) : α ≃ γ := g.trans h

instance : FunLike (Equiv α β) α β where
  coe := toFun
  coe_inj := by
    intro a b eq
    suffices a.invFun = b.invFun by
      cases a; cases b; congr
    ext x
    apply a.leftInv.Injective
    rw [a.rightInv, eq, b.rightInv]

def inj (h: α ≃ b) : Function.Injective h := h.leftInv.Injective
def surj (h: α ≃ b) : Function.Surjective h := h.rightInv.Surjective

def toEmbedding (h: α ≃ β) : α ↪ β where
  toFun := h
  inj' := inj h

def toSurjection (h: α ≃ β) : α ↠ β where
  toFun := h
  surj' := surj h

def toBijection (h: α ≃ β) : α ⇆ β := {
  h.toEmbedding, h.toSurjection with
}

@[simp] def apply_toEmbedding (h: α ≃ β) : (h.toEmbedding: α -> β) = h := rfl
@[simp] def apply_toSurjection (h: α ≃ β) : (h.toSurjection: α -> β) = h := rfl
@[simp] def apply_toBijection (h: α ≃ β) : (h.toBijection: α -> β) = h := rfl

@[simp]
def toEmbedding_trans (h: α ≃ β) (g: β ≃ γ) : h.toEmbedding.trans g.toEmbedding = (h.trans g).toEmbedding := rfl

def copy (f: α ≃ β) (g₀: α -> β) (g₁: β -> α) (h₀: f = g₀) (h₁: f.symm = g₁) : α ≃ β where
  toFun := g₀
  invFun := g₁
  leftInv := h₀ ▸ h₁ ▸ f.leftInv
  rightInv := h₀ ▸ h₁ ▸ f.rightInv

@[ext]
def ext (a b: α ≃ β) : (∀x, a x = b x) -> a = b := DFunLike.ext _ _

def trans_assoc {h₀: α₀ ≃ α₁} {h₁: α₁ ≃  α₂} {h₂: α₂ ≃  α₃} :
  (h₀.trans h₁).trans h₂ = h₀.trans (h₁.trans h₂) := by rfl

@[simp] def coe_symm (h: α ≃ β) (x: α) : h.symm (h x) = x := h.leftInv _
@[simp] def symm_coe (h: α ≃ β) (x: β) : h (h.symm x) = x := h.rightInv _

@[simp] def apply_trans {α β γ: Sort*} (h: α ≃ β) (g: β ≃ γ) (x: α) : (h.trans g) x = g (h x) := by rfl

def trans_symm (h: α ≃ β) : h.trans h.symm = .rfl := by
  ext x
  show h.symm (h x) = x
  rw [h.coe_symm]

def symm_trans (h: α ≃ β) : h.symm.trans h = .rfl := by
  ext x
  show h (h.symm x) = x
  rw [h.symm_coe]

def ofBij {f: α -> β} (b: Function.Bijective f) : ∃x: Equiv α β, x = f := by
  have ⟨finv, finvdef⟩ := b.Surjective.exists_inv
  refine ⟨?_, ?_⟩
  apply Equiv.mk f finv _ _
  intro x
  apply b.Injective
  rw [←finvdef]
  intro x
  symm; apply finvdef
  rfl

instance : Coe (α ≃ β) (α ↪ β) := ⟨toEmbedding⟩

def equivIff {P Q: Prop} : (P ≃ Q) ≃ (P ↔ Q) where
  toFun h := ⟨h, h.symm⟩
  invFun h := ⟨h.mp, h.mpr, fun _ => proof_irrel _ _, fun _ => proof_irrel _ _⟩
  leftInv x := by rfl
  rightInv x := by rfl

def equiv_symm {α β: Sort*} : (α ≃ β) ≃ (β ≃ α) where
  toFun := symm
  invFun := symm
  leftInv x := by rfl
  rightInv x := by rfl

def eq_coe_of_symm_eq (h: α ≃ β) : h.symm x = y -> x = h y := by
  intro g
  rw [←g, symm_coe]

def eq_symm_of_coe_eq (h: α ≃ β) : h x = y -> x = h.symm y := by
  intro g
  rw [←g, coe_symm]

@[simp] def symm_symm (h: α ≃ β) : h.symm.symm = h := rfl

@[simp]
def mk_apply (f: α -> β) (g: β -> α) (h: Function.IsLeftInverse f g) (h': Function.IsRightInverse f g) (x: α) : Equiv.mk f g h' h x = f x := by rfl

protected def Nonempty [g: Nonempty α] (h: α ≃ β) : Nonempty β :=
  have ⟨x⟩ := g
  ⟨h x⟩

@[simp] def toFun_eq_coe (f: α ≃ β) : f.toFun = f := rfl
@[simp] def toEmbedding_eq_coe (f: α ≃ β) : (f.toEmbedding: _ -> _) = f := rfl

@[simp] def coe_mk (f: α -> β) (g: β -> α) (hf: Function.IsRightInverse f g) (hg: Function.IsLeftInverse f g) : Equiv.mk f g hf hg = f := rfl

@[simp] def symm_mk (f: α -> β) (g: β -> α) (hf: Function.IsRightInverse f g) (hg: Function.IsLeftInverse f g) : (Equiv.mk f g hf hg).symm = (Equiv.mk g f hg hf) := rfl

@[simp] def symm_trans' : (Equiv.trans h g).symm = Equiv.trans g.symm h.symm := rfl

@[simp] def apply_refl : Equiv.refl _ x = x := rfl
@[simp] def apply_rfl : Equiv.rfl x = x := rfl

def symm.inj : Function.Injective (Equiv.symm (α := α) (β := β)) := by
  intro x y h
  ext a
  rw (occs := [2]) [←x.coe_symm a]
  rw [h]; simp

@[simp]
def refl_toEmbedding : (Equiv.rfl : α ≃ α).toEmbedding = .rfl := rfl

def ofInvolut (f: α -> α) (h: f.IsInvolutive) : α ≃ α where
  toFun := f
  invFun := f
  leftInv := h
  rightInv := h

def congr {f g: α ≃ β} (h: f = g) : ∀x, f x = g x := fun _ => h ▸ rfl

@[simp]
def trans_left (f: α ≃ β) (g h: β ≃ γ) : f.trans g = f.trans h ↔ g = h := by
  apply Iff.intro
  · intro eq; ext x
    have := congr eq (f.symm x)
    simpa using this
  · intro h; rw [h]

@[simp]
def trans_right (g h: α ≃ β) (f: β ≃ γ) : g.trans f = h.trans f ↔ g = h := by
  apply Iff.intro
  · intro eq; ext x
    exact f.inj (congr eq x)
  · intro h; rw [h]

end Equiv

namespace Bijection

noncomputable def toEquiv (f: α ⇆ β) : α ≃ β := Classical.choose (Equiv.ofBij f.bij)
noncomputable def toEquiv_spec (f: α ⇆ β) : (f.toEquiv: α -> β) = f := Classical.choose_spec (Equiv.ofBij f.bij)

noncomputable def symm (f: α ⇆ β) : β ⇆ α :=
  f.toEquiv.symm.toBijection

@[simp] def coe_symm (h: α ⇆ β) (x: α) : h.symm (h x) = x := by
  rw [←h.toEquiv_spec, symm]; simp
@[simp] def symm_coe (h: α ⇆ β) (x: β) : h (h.symm x) = x := by
  rw [←h.toEquiv_spec, symm]; simp

@[simp] def apply_trans (f: α ⇆ β) (g: β ⇆ γ) (x: α) : f.trans g x = g (f x) := rfl

@[simp] def apply_mk (f: α -> β) (h₀: f.Injective) (h₁: f.Surjective) : ({ toFun := f, inj' := h₀, surj' := h₁ }: α ⇆ β) = f := rfl

end Bijection
