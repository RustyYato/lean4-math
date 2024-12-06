import Math.Function.Basic
import Math.Data.Like.Equiv

class IsEmpty (α: Sort*): Prop where
  elim: α -> False

def elim_empty [IsEmpty α] : α -> False := IsEmpty.elim

instance : IsEmpty False := ⟨id⟩
instance : IsEmpty PEmpty := ⟨PEmpty.elim⟩
instance : IsEmpty Empty := ⟨Empty.elim⟩
instance {α: Sort*} {β: α -> Sort*} [Inhabited α] [IsEmpty (β default)] : IsEmpty (∀x, β x) where
  elim f := elim_empty (f default)
instance {α: Type*} {β: α -> Type*} [∀x, IsEmpty (β x)] : IsEmpty ((x: α) × β x) where
  elim f := elim_empty f.2
instance {α: Sort*} {β: α -> Sort*} [∀x, IsEmpty (β x)] : IsEmpty ((x: α) ×' β x) where
  elim f := elim_empty f.2
instance {α: Type*} {β: α -> Type*} [IsEmpty α] : IsEmpty ((x: α) × β x) where
  elim f := elim_empty f.1
instance {α: Sort*} {β: α -> Sort*} [IsEmpty α] : IsEmpty ((x: α) ×' β x) where
  elim f := elim_empty f.1
instance {α: Type*} {β: Type*} [IsEmpty α] : IsEmpty (α × β) where
  elim f := elim_empty f.1
instance {α: Sort*} {β: Sort*} [IsEmpty α] : IsEmpty (α ×' β) where
  elim f := elim_empty f.1
instance {α: Type*} {β: Type*} [IsEmpty α] [IsEmpty β] : IsEmpty (α ⊕ β) where
  elim f := (by cases f <;> (rename_i f; exact elim_empty f))
instance {α: Sort*} {β: Sort*} [IsEmpty α] [IsEmpty β] : IsEmpty (α ⊕' β) where
  elim f := (by cases f <;> (rename_i f; exact elim_empty f))
instance {α: Prop} {β: Prop} [IsEmpty α] : IsEmpty (α ∧ β) where
  elim f := elim_empty f.1
instance {α: Prop} {β: Prop} [IsEmpty β] : IsEmpty (α ∧ β) where
  elim f := elim_empty f.2
instance {α: Prop} {β: Prop} [IsEmpty α] [IsEmpty β] : IsEmpty (α ∨ β) where
  elim f := (by cases f <;> (rename_i f; exact elim_empty f))

structure Embedding (α β: Sort*) where
  toFun: α -> β
  inj: Function.Injective toFun

infixr:25 " ↪ " => Embedding

structure Equiv (α β: Sort*) where
  toFun: α -> β
  invFun: β -> α
  leftInv: invFun.IsLeftInverse toFun
  rightInv: invFun.IsRightInverse toFun

infixl:25 " ≃ " => Equiv

def Equiv.toFun_inj (h: α ≃ b) : Function.Injective h.toFun := h.leftInv.Injective
def Equiv.invFun_inj (h: α ≃ b) : Function.Injective h.invFun := h.rightInv.Injective

def Equiv.toEmbedding (h: α ≃ β) : α ↪ β where
  toFun := h.toFun
  inj := h.toFun_inj

instance : FunLike (α ↪ β) α β where
  coe e := e.toFun
  coe_inj x y h := by cases x; cases y; congr

instance : IsEmbeddingLike (α ↪ β) α β where
  coe_inj e := e.inj

instance : IsEquivLike (α ≃ β) α β where
  coe e := e.toFun
  inv e := e.invFun
  leftInv e := e.leftInv
  rightInv e := e.rightInv
  inj a b h g := by cases a; cases b; congr

@[refl]
def Equiv.refl : Equiv α α where
  toFun := id
  invFun := id
  leftInv _ := rfl
  rightInv _ := rfl

@[symm]
def Equiv.symm (h: Equiv α β) : Equiv β α where
  toFun := h.invFun
  invFun := h.toFun
  leftInv := h.rightInv
  rightInv := h.leftInv

def Equiv.trans (h: Equiv α β) (g: Equiv β γ) : Equiv α γ where
  toFun := g.toFun ∘ h.toFun
  invFun := h.invFun ∘ g.invFun
  leftInv x := by
    dsimp
    rw [g.leftInv, h.leftInv]
  rightInv x := by
    dsimp
    rw [h.rightInv, g.rightInv]

instance [IsEmpty α] : Embedding α β where
  toFun x := (elim_empty x).elim
  inj x := (elim_empty x).elim

def Equiv.ofBij {f: α -> β} (b: Function.Bijective f) : ∃x: Equiv α β, x = f := by
  have ⟨finv, finvdef⟩ := b.Surjective.exists_inv
  refine ⟨?_, ?_⟩
  apply Equiv.mk f finv _ finvdef
  intro x
  apply b.Injective
  rw [finvdef]
  rfl

def Embedding.comp (b: β ↪ γ) (a: α ↪ β) : α ↪ γ where
  toFun := b.toFun ∘ a.toFun
  inj := Function.Injective.comp b.inj a.inj
