import Math.Logic.Equiv.Like
import Math.Data.Like.Func
import Math.Order.Defs
import Math.Order.Monotone.Defs

variable {F α β γ}
  [LE α] [LE β] [LE γ] [LT α] [LT β] [LT γ]
  [Top α] [Top β] [Top γ] [Bot α] [Bot β] [Bot γ]
  [Min α] [Min β] [Min γ] [Max α] [Max β] [Max γ]

class IsMinHom (F α β: Type*) [FunLike F α β] [Min α] [Min β] where
  protected map_min (f: F) (a b: α) : f (a ⊓ b) = f a ⊓ f b := by intro f; exact f.map_min

class IsMaxHom (F α β: Type*) [FunLike F α β] [Max α] [Max β] where
  protected map_max (f: F) (a b: α) : f (a ⊔ b) = f a ⊔ f b := by intro f; exact f.map_max

class IsTopHom (F α β: Type*) [FunLike F α β] [Top α] [Top β] where
  protected map_top (f: F) : f ⊤ = ⊤

class IsBotHom (F α β: Type*) [FunLike F α β] [Bot α] [Bot β] where
  protected map_bot (f: F) : f ⊥ = ⊥

def map_min [FunLike F α β] [IsMinHom F α β] (f: F) (a b: α) : f (a ⊓ b) = f a ⊓ f b := IsMinHom.map_min _ _ _
def map_max [FunLike F α β] [IsMaxHom F α β] (f: F) (a b: α) : f (a ⊔ b) = f a ⊔ f b := IsMaxHom.map_max _ _ _

def map_top [FunLike F α β] [IsTopHom F α β] (f: F) : f ⊤ = ⊤ := IsTopHom.map_top _
def map_bot [FunLike F α β] [IsBotHom F α β] (f: F) : f ⊥ = ⊥ := IsBotHom.map_bot _

structure MinHom (α β: Type*) [Min α] [Min β] where
  toFun: α -> β
  protected map_min (a b: α) : toFun (a ⊓ b) = toFun a ⊓ toFun b

instance : FunLike (MinHom α β) α β where
instance : IsMinHom (MinHom α β) α β where

structure MaxHom (α β: Type*) [Max α] [Max β] where
  toFun: α -> β
  protected map_max (a b: α) : toFun (a ⊔ b) = toFun a ⊔ toFun b

instance : FunLike (MaxHom α β) α β where
instance : IsMaxHom (MaxHom α β) α β where

structure MinEmbedding (α β: Type*) [Min α] [Min β] extends α ↪ β, MinHom α β where

instance : EmbeddingLike (MinEmbedding α β) α β where
instance : IsMinHom (MinEmbedding α β) α β where

structure MaxEmbedding (α β: Type*) [Max α] [Max β] extends α ↪ β, MaxHom α β where

instance : EmbeddingLike (MaxEmbedding α β) α β where
instance : IsMaxHom (MaxEmbedding α β) α β where

structure MinEquiv (α β: Type*) [Min α] [Min β] extends α ≃ β, MinHom α β where

instance : EquivLike (MinEquiv α β) α β where
instance : IsMinHom (MinEquiv α β) α β where

structure MaxEquiv (α β: Type*) [Max α] [Max β] extends α ≃ β, MaxHom α β where

instance : EquivLike (MaxEquiv α β) α β where
instance : IsMaxHom (MaxEquiv α β) α β where

structure LatticeHom (α β: Type*) [Min α] [Min β] [Max α] [Max β] extends MinHom α β, MaxHom α β where

instance : FunLike (LatticeHom α β) α β where

instance : IsMinHom (LatticeHom α β) α β where
instance : IsMaxHom (LatticeHom α β) α β where

structure LatticeEmbedding (α β: Type*) [Min α] [Min β] [Max α] [Max β] extends α ↪ β, MinEmbedding α β, MaxEmbedding α β where

instance : EmbeddingLike (LatticeEmbedding α β) α β where

instance : IsMinHom (LatticeEmbedding α β) α β where
instance : IsMaxHom (LatticeEmbedding α β) α β where

structure LatticeEquiv (α β: Type*) [Min α] [Min β] [Max α] [Max β] extends α ≃ β, MinEquiv α β, MaxEquiv α β where

instance : EquivLike (LatticeEquiv α β) α β where

instance : IsMinHom (LatticeEquiv α β) α β where
instance : IsMaxHom (LatticeEquiv α β) α β where

infixr:25 " →≤ " => MinHom
infixr:25 " ↪≤ " => MinEmbedding
infixr:25 " ≃≤ " => MinEquiv

infixr:25 " →⊓ " => MinHom
infixr:25 " ↪⊓ " => MinEmbedding
infixr:25 " ≃⊓ " => MinEquiv

infixr:25 " →⊔ " => MaxHom
infixr:25 " ↪⊔ " => MaxEmbedding
infixr:25 " ≃⊔ " => MaxEquiv

infixr:25 " →⊓⊔ " => LatticeHom
infixr:25 " ↪⊓⊔ " => LatticeEmbedding
infixr:25 " ≃⊓⊔ " => LatticeEquiv

protected def MinHom.id (α: Type*) [Min α] : α →⊓ α where
  toFun := id
  map_min _ _ := rfl
protected def MaxHom.id (α: Type*) [Max α] : α →⊔ α where
  toFun := id
  map_max _ _ := rfl
protected def LatticeHom.id (α: Type*) [Min α] [Max α] : α →⊓⊔ α := {
  MinHom.id α, MaxHom.id α with
}
protected def MinEmbedding.refl (α: Type*) [Min α] : α ↪⊓ α where
  toEmbedding := .refl _
  map_min _ _ := rfl
protected def MaxEmbedding.refl (α: Type*) [Max α] : α ↪⊔ α where
  toEmbedding := .refl _
  map_max _ _ := rfl
protected def LatticeEmbedding.refl (α: Type*) [Min α] [Max α] : α ↪⊓⊔ α := {
  MinEmbedding.refl α, MaxEmbedding.refl α with
}
protected def MinEquiv.refl (α: Type*) [Min α] : α ≃⊓ α where
  toEquiv := .refl _
  map_min _ _ := rfl
protected def MaxEquiv.refl (α: Type*) [Max α] : α ≃⊔ α where
  toEquiv := .refl _
  map_max _ _ := rfl
protected def LatticeEquiv.refl (α: Type*) [Min α] [Max α] : α ≃⊓⊔ α := {
  MinEquiv.refl α, MaxEquiv.refl α with
}

def MinHom.comp (f: β →⊓ γ) (g: α →⊓ β) : α →⊓ γ where
  toFun := f ∘ g
  map_min a b := by
    dsimp [Function.comp_def]
    rw [map_min, map_min]
def MaxHom.comp (f: β →⊔ γ) (g: α →⊔ β) : α →⊔ γ where
  toFun := f ∘ g
  map_max a b := by
    dsimp [Function.comp_def]
    rw [map_max, map_max]
def LatticeHom.comp (f: β →⊓⊔ γ) (g: α →⊓⊔ β) : α →⊓⊔ γ := {
  f.toMinHom.comp g.toMinHom, f.toMaxHom.comp g.toMaxHom with
}

def MinEmbedding.trans (f: α ↪⊓ β) (g: β ↪⊓ γ) : α ↪⊓ γ := {
  g.toMinHom.comp f.toMinHom, f.toEmbedding.trans g.toEmbedding with
}
def MaxEmbedding.trans (f: α ↪⊔ β) (g: β ↪⊔ γ) : α ↪⊔ γ := {
  g.toMaxHom.comp f.toMaxHom, f.toEmbedding.trans g.toEmbedding with
}
def LatticeEmbedding.trans (f: α ↪⊓⊔ β) (g: β ↪⊓⊔ γ) : α ↪⊓⊔ γ := {
  f.toMinEmbedding.trans g.toMinEmbedding, f.toMaxEmbedding.trans g.toMaxEmbedding with
}

def MinEquiv.trans (f: α ≃⊓ β) (g: β ≃⊓ γ) : α ≃⊓ γ := {
  g.toMinHom.comp f.toMinHom, f.toEquiv.trans g.toEquiv with
}
def MaxEquiv.trans (f: α ≃⊔ β) (g: β ≃⊔ γ) : α ≃⊔ γ := {
  g.toMaxHom.comp f.toMaxHom, f.toEquiv.trans g.toEquiv with
}
def LatticeEquiv.trans (f: α ≃⊓⊔ β) (g: β ≃⊓⊔ γ) : α ≃⊓⊔ γ := {
  f.toMinEquiv.trans g.toMinEquiv, f.toMaxEquiv.trans g.toMaxEquiv with
}

def MinEquiv.symm (f: α ≃⊓ β) : β ≃⊓ α := {
  f.toEquiv.symm with
  map_min a b := by
    simp
    apply f.inj
    show _ = f _
    rw [map_min f, f.symm_coe]
    symm; congr <;> apply Equiv.symm_coe
}
def MaxEquiv.symm (f: α ≃⊔ β) : β ≃⊔ α := {
  f.toEquiv.symm with
  map_max a b := by
    simp
    apply f.inj
    show _ = f _
    rw [map_max f, f.symm_coe]
    symm; congr <;> apply Equiv.symm_coe
}
def LatticeEquiv.symm (f: α ≃⊓⊔ β) : β ≃⊓⊔ α := {
  f.toMinEquiv.symm, f.toMaxEquiv.symm with
}

def MinEmbedding.toHom (f: α ↪⊓ β) : α →⊓ β := { f with }
def MaxEmbedding.toHom (f: α ↪⊔ β) : α →⊔ β := { f with }
def LatticeEmbedding.toHom (f: α ↪⊓⊔ β) : α →⊓⊔ β := { f with }
def MinEquiv.toEmbedding (f: α ≃⊓ β) : α ↪⊓ β := { f, f.toEquiv.toEmbedding with }
def MaxEquiv.toEmbedding (f: α ≃⊔ β) : α ↪⊔ β := { f, f.toEquiv.toEmbedding with }
def LatticeEquiv.toEmbedding (f: α ≃⊓⊔ β) : α ↪⊓⊔ β := { f, f.toEquiv.toEmbedding with }
def MinEquiv.toHom (f: α ≃⊓ β) : α →⊓ β := { f with }
def MaxEquiv.toHom (f: α ≃⊔ β) : α →⊔ β := { f with }
def LatticeEquiv.toHom (f: α ≃⊓⊔ β) : α →⊓⊔ β := { f with }
