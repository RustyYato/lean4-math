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

namespace Embedding

@[refl]
def refl (α: Sort*) : α ↪ α where
  toFun := id
  inj' := fun _ _ => id

def rfl {α: Sort*} : α ↪ α := .refl _

def trans {α β γ: Sort*} (h: α ↪ β) (g: β ↪ γ) : α ↪ γ where
  toFun := g.toFun ∘ h.toFun
  inj' := Function.Injective.comp g.inj' h.inj'

abbrev comp {α β γ: Sort*} (h: β ↪ γ) (g: α ↪ β) : α ↪ γ := g.trans h

instance : FunLike (Embedding α β) α β where
  coe := toFun
  coe_inj := by
    intro a b eq
    cases a; cases b; congr

def inj (h: α ↪ b) : Function.Injective h := h.inj'

@[ext]
def ext (a b: α ↪ β) : (∀x, a x = b x) -> a = b := DFunLike.ext _ _

@[simp]
def mk_apply (f: α -> β) (h: Function.Injective f) (x: α) : Embedding.mk f h x = f x := by rfl

end Embedding

namespace Equiv

@[refl]
def refl (α: Sort*) : α ≃ α where
  toFun := id
  invFun := id
  leftInv _ := rfl
  rightInv _ := rfl

def rfl {α: Sort*} : α ≃ α := .refl _

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

def toEmbedding (h: α ≃ β) : α ↪ β where
  toFun := h
  inj' := inj h

@[ext]
def ext (a b: α ≃ β) : (∀x, a x = b x) -> a = b := DFunLike.ext _ _

def trans_assoc {h₀: α₀ ≃ α₁} {h₁: α₁ ≃  α₂} {h₂: α₂ ≃  α₃} :
  (h₀.trans h₁).trans h₂ = h₀.trans (h₁.trans h₂) := by rfl

def coe_symm (h: α ≃ β) (x: α) : h.symm (h x) = x := h.leftInv _
def symm_coe (h: α ≃ β) (x: β) : h (h.symm x) = x := h.rightInv _

def apply_trans {α β γ: Sort*} (h: α ≃ β) (g: β ≃ γ) (x: α) : (h.trans g) x = g (h x) := by rfl

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

def symm_symm (h: α ≃ β) : h.symm.symm = h := _root_.rfl

@[simp]
def mk_apply (f: α -> β) (g: β -> α) (h: Function.IsLeftInverse f g) (h': Function.IsRightInverse f g) (x: α) : Equiv.mk f g h' h x = f x := by rfl

protected def Nonempty [g: Nonempty α] (h: α ≃ β) : Nonempty β :=
  have ⟨x⟩ := g
  ⟨h x⟩

end Equiv
