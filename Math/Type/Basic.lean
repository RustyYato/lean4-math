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

class Embedding (α β: Sort*) where
  toFun: α -> β
  inj: Function.Injective toFun

infixr:25 "↪" => Embedding

class Equiv (α β: Sort*) where
  toFun: α -> β
  invFun: β -> α
  leftInv: invFun.IsLeftInverse toFun
  rightInv: invFun.IsRightInverse toFun

infixl:25 "≃" => Equiv

def Equiv.toFun.inj (h: α ≃ b) : Function.Injective h.toFun := h.leftInv.Injective
def Equiv.invFun.inj (h: α ≃ b) : Function.Injective h.invFun := h.rightInv.Injective

instance [h: Equiv α β] : Embedding α β where
  toFun := h.toFun
  inj := Equiv.toFun.inj h

instance [h: Equiv α β] : Embedding β α where
  toFun := h.invFun
  inj := Equiv.invFun.inj h

instance : FunLike (Embedding α β) α β where
  coe e := e.toFun
  coe_inj x y h := by cases x; cases y; congr

instance : IsEmbeddingLike (Embedding α β) α β where
  coe_inj e := e.inj

instance : IsEquivLike (Equiv α β) α β where
  coe e := e.toFun
  inv e := e.invFun
  leftInv e := e.leftInv
  rightInv e := e.rightInv
  inj a b h g := by cases a; cases b; congr

@[refl]
instance Equiv.refl : Equiv α α where
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

-- low priority so that if there is a custom instance, it will be wed
instance (priority := 100) [h: Equiv α β] : Equiv β α := h.symm

instance [IsEmpty α] : Embedding α β where
  toFun x := (elim_empty x).elim
  inj x := (elim_empty x).elim
