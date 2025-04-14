import Math.Logic.Equiv.Like
import Math.Data.Like.Func
import Math.Order.Defs
import Math.Order.Monotone.Defs

section

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

class IsMonotoneHom (F α β: Type*) [FunLike F α β] [LE α] [LE β] where
  protected monotone (f: F) : Monotone f := by intro f; exact f.monotone

class IsStrictMonotoneHom (F α β: Type*) [FunLike F α β] [LT α] [LT β] where
  protected strict_monotone (f: F) : StrictMonotone f := by intro f; exact f.strict_monotone

class IsOrderHom (F α β: Type*) [FunLike F α β] [LE α] [LE β] where
  protected map_le (f: F) (a b: α) : a ≤ b ↔ f a ≤ f b := by intro f; exact f.map_le

class IsStrictOrderHom (F α β: Type*) [FunLike F α β] [LT α] [LT β] where
  protected map_lt (f: F) (a b: α) : a < b ↔ f a < f b := by intro f; exact f.map_lt

def map_min [FunLike F α β] [IsMinHom F α β] (f: F) (a b: α) : f (a ⊓ b) = f a ⊓ f b := IsMinHom.map_min _ _ _
def map_max [FunLike F α β] [IsMaxHom F α β] (f: F) (a b: α) : f (a ⊔ b) = f a ⊔ f b := IsMaxHom.map_max _ _ _

def map_top [FunLike F α β] [IsTopHom F α β] (f: F) : f ⊤ = ⊤ := IsTopHom.map_top _
def map_bot [FunLike F α β] [IsBotHom F α β] (f: F) : f ⊥ = ⊥ := IsBotHom.map_bot _

def map_monotone [FunLike F α β] [LE α] [LE β] [IsMonotoneHom F α β] (f: F) : Monotone f := IsMonotoneHom.monotone _
def map_strict_monotone [FunLike F α β] [LE α] [LE β] [IsStrictMonotoneHom F α β] (f: F) : StrictMonotone f := IsStrictMonotoneHom.strict_monotone _
def map_le [FunLike F α β] [LE α] [LE β] [IsOrderHom F α β] (f: F) {a b: α} : a ≤ b ↔ f a ≤ f b := IsOrderHom.map_le _ _ _
def map_lt [FunLike F α β] [LT α] [LT β] [IsStrictOrderHom F α β] (f: F) {a b: α} : a < b ↔ f a < f b := IsStrictOrderHom.map_lt _ _ _

instance [FunLike F α β] [IsOrderHom F α β] : IsMonotoneHom F α β where
  monotone _ _ _ := (map_le _).mp
instance [FunLike F α β] [IsStrictOrderHom F α β] : IsStrictMonotoneHom F α β where
  strict_monotone _ _ _ := (map_lt _).mp
instance (priority := 500) [FunLike F α β] [IsOrderHom F α β] [IsLawfulLT α] [IsLawfulLT β] : IsStrictOrderHom F α β where
  map_lt f a b := by rw [lt_iff_le_and_not_le, lt_iff_le_and_not_le, ←map_le, ←map_le]
instance (priority := 500) [EmbeddingLike F α β] [IsStrictOrderHom F α β] [IsPartialOrder α] [IsPartialOrder β] : IsOrderHom F α β where
  map_le f a b := by
    apply Iff.intro
    intro h
    cases lt_or_eq_of_le h
    apply le_of_lt; apply (map_lt _).mp
    assumption
    subst b; rfl
    intro h
    cases lt_or_eq_of_le h
    apply le_of_lt; apply (map_lt f).mpr
    assumption
    apply le_of_eq; apply (f: α ↪ β).inj
    assumption
instance [FunLike F α β] [IsMinHom F α β] [IsSemiLatticeMin α] [IsSemiLatticeMin β] : IsMonotoneHom F α β where
  monotone f a b := by
    rw [←min_eq_left, ←min_eq_left]
    rw [←map_min]
    intro h
    rw [h]
instance [FunLike F α β] [IsMaxHom F α β] [IsSemiLatticeMax α] [IsSemiLatticeMax β] : IsMonotoneHom F α β where
  monotone f a b := by
    rw [←max_eq_left, ←max_eq_left]
    rw [←map_max]
    intro h
    rw [h]
instance instFoo [EmbeddingLike F α β] [IsMinHom F α β] [IsSemiLatticeMin α] [IsSemiLatticeMin β] : IsOrderHom F α β where
  map_le f a b := by
    apply min_eq_left.symm.trans
    apply Iff.trans _ min_eq_left
    rw [←map_min]
    apply (f: α ↪ β).inj.eq_iff.symm
instance [EmbeddingLike F α β] [IsMaxHom F α β] [IsSemiLatticeMax α] [IsSemiLatticeMax β] : IsOrderHom F α β where
  map_le f a b := by
    apply max_eq_left.symm.trans
    apply Iff.trans _ max_eq_left
    rw [←map_max]
    apply (f: α ↪ β).inj.eq_iff.symm
instance [FunLike F α β] [IsSurjective F α β] [IsOrderHom F α β] [IsPartialOrder α] [IsPartialOrder β] [IsLawfulTop α] [IsLawfulTop β] : IsTopHom F α β where
  map_top f := by
    apply le_antisymm
    apply le_top
    have ⟨x, eq⟩ := coe_surj f ⊤
    rw [eq]
    apply map_monotone
    apply le_top
instance [FunLike F α β] [IsSurjective F α β] [IsOrderHom F α β] [IsPartialOrder α] [IsPartialOrder β] [IsLawfulBot α] [IsLawfulBot β] : IsBotHom F α β where
  map_bot f := by
    apply le_antisymm
    have ⟨x, eq⟩ := coe_surj f ⊥
    rw [eq]
    apply map_monotone
    apply bot_le
    apply bot_le
instance [FunLike F α β] [IsStrictMonotoneHom F α β] [IsLinearOrder α] [IsPreOrder β] : EmbeddingLike F α β where
  coe f := {
    toFun := f
    inj' := by
      intro x y h
      apply Relation.eq_of_not_lt_or_gt (· < ·)
      intro g
      have := map_strict_monotone f g
      rw [h] at this
      exact lt_irrefl this
      intro g
      have := map_strict_monotone f g
      rw [h] at this
      exact lt_irrefl this
  }
  coe_inj a b h := by
    dsimp at h
    apply DFunLike.ext
    intro
    rw [Embedding.mk.inj h]

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

structure MonotoneHom (α β: Type*) [LE α] [LE β] where
  toFun: α -> β
  protected monotone: Monotone toFun

instance : FunLike (MonotoneHom α β) α β where
instance : IsMonotoneHom (MonotoneHom α β) α β where

structure StrictMonotoneHom (α β: Type*) [LT α] [LT β] where
  toFun: α -> β
  protected strict_monotone: StrictMonotone toFun

instance : FunLike (StrictMonotoneHom α β) α β where
instance : IsStrictMonotoneHom (StrictMonotoneHom α β) α β where

structure OrderHom (α β: Type*) [LE α] [LE β] where
  toFun: α -> β
  protected map_le (a b: α): a ≤ b ↔ toFun a ≤ toFun b

instance : FunLike (OrderHom α β) α β where
instance : IsOrderHom (OrderHom α β) α β where

structure MinEmbedding (α β: Type*) [Min α] [Min β] extends α ↪ β, MinHom α β where

instance : EmbeddingLike (MinEmbedding α β) α β where
instance : IsMinHom (MinEmbedding α β) α β where

structure MaxEmbedding (α β: Type*) [Max α] [Max β] extends α ↪ β, MaxHom α β where

instance : EmbeddingLike (MaxEmbedding α β) α β where
instance : IsMaxHom (MaxEmbedding α β) α β where

structure OrderEmbedding (α β: Type*) [LE α] [LE β] extends α ↪ β, OrderHom α β where

instance : EmbeddingLike (OrderEmbedding α β) α β where
instance : IsOrderHom (OrderEmbedding α β) α β where

structure MinEquiv (α β: Type*) [Min α] [Min β] extends α ≃ β, MinHom α β where

instance : EquivLike (MinEquiv α β) α β where
instance : IsMinHom (MinEquiv α β) α β where

structure MaxEquiv (α β: Type*) [Max α] [Max β] extends α ≃ β, MaxHom α β where

instance : EquivLike (MaxEquiv α β) α β where
instance : IsMaxHom (MaxEquiv α β) α β where

structure OrderEquiv (α β: Type*) [LE α] [LE β] extends α ≃ β, OrderHom α β where

instance : EquivLike (OrderEquiv α β) α β where
instance : IsOrderHom (OrderEquiv α β) α β where

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

infixr:25 " →≤ " => MonotoneHom
infixr:25 " →< " => StrictMonotoneHom

infixr:25 " →o " => OrderHom
infixr:25 " ↪o " => OrderEmbedding
infixr:25 " ≃o " => OrderEquiv

infixr:25 " →⊓ " => MinHom
infixr:25 " ↪⊓ " => MinEmbedding
infixr:25 " ≃⊓ " => MinEquiv

infixr:25 " →⊔ " => MaxHom
infixr:25 " ↪⊔ " => MaxEmbedding
infixr:25 " ≃⊔ " => MaxEquiv

infixr:25 " →⊓⊔ " => LatticeHom
infixr:25 " ↪⊓⊔ " => LatticeEmbedding
infixr:25 " ≃⊓⊔ " => LatticeEquiv

end

@[refl] protected def MinHom.id (α: Type*) [Min α] : α →⊓ α where
  toFun := id
  map_min _ _ := rfl
@[refl] protected def MaxHom.id (α: Type*) [Max α] : α →⊔ α where
  toFun := id
  map_max _ _ := rfl
@[refl] protected def LatticeHom.id (α: Type*) [Min α] [Max α] : α →⊓⊔ α := {
  MinHom.id α, MaxHom.id α with
}
@[refl] protected def MonotoneHom.id (α: Type*) [LE α] : α →≤ α where
  toFun := id
  monotone := Monotone.id
@[refl] protected def StrictMonotoneHom.id (α: Type*) [LT α] : α →< α where
  toFun := id
  strict_monotone := StrictMonotone.id
@[refl] protected def OrderHom.id (α: Type*) [LE α] : α →o α where
  toFun := id
  map_le _ _ := Iff.rfl

@[refl] protected def MinEmbedding.refl (α: Type*) [Min α] : α ↪⊓ α where
  toEmbedding := .refl _
  map_min _ _ := rfl
@[refl] protected def MaxEmbedding.refl (α: Type*) [Max α] : α ↪⊔ α where
  toEmbedding := .refl _
  map_max _ _ := rfl
@[refl] protected def LatticeEmbedding.refl (α: Type*) [Min α] [Max α] : α ↪⊓⊔ α := {
  MinEmbedding.refl α, MaxEmbedding.refl α with
}
@[refl] protected def OrderEmbedding.refl (α: Type*) [LE α] : α ↪o α where
  toEmbedding := .refl _
  map_le _ _ := Iff.rfl
@[refl] protected def MinEquiv.refl (α: Type*) [Min α] : α ≃⊓ α where
  toEquiv := .refl _
  map_min _ _ := rfl
@[refl] protected def MaxEquiv.refl (α: Type*) [Max α] : α ≃⊔ α where
  toEquiv := .refl _
  map_max _ _ := rfl
@[refl] protected def LatticeEquiv.refl (α: Type*) [Min α] [Max α] : α ≃⊓⊔ α := {
  MinEquiv.refl α, MaxEquiv.refl α with
}
@[refl] protected def OrderEquiv.refl (α: Type*) [LE α] : α ≃o α where
  toEquiv := .refl _
  map_le _ _ := Iff.rfl


variable {F α β γ}
  {_: LE α} {_: LE β} {_: LE γ} {_: LT α} {_: LT β} {_: LT γ}
  {_: Top α} {_: Top β} {_: Top γ} {_: Bot α} {_: Bot β} {_: Bot γ}
  {_: Min α} {_: Min β} {_: Min γ} {_: Max α} {_: Max β} {_: Max γ}

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
def MonotoneHom.comp (f: β →≤ γ) (g: α →≤ β) : α →≤ γ where
  toFun := f ∘ g
  monotone := Monotone.comp f.monotone g.monotone
def StrictMonotoneHom.comp (f: β →< γ) (g: α →< β) : α →< γ where
  toFun := f ∘ g
  strict_monotone := StrictMonotone.comp g.strict_monotone f.strict_monotone
def OrderHom.comp (f: β →o γ) (g: α →o β) : α →o γ where
  toFun := f ∘ g
  map_le _ _ := Iff.trans (g.map_le  _ _) (f.map_le  _ _)

def MinEmbedding.trans (f: α ↪⊓ β) (g: β ↪⊓ γ) : α ↪⊓ γ := {
  g.toMinHom.comp f.toMinHom, f.toEmbedding.trans g.toEmbedding with
}
def MaxEmbedding.trans (f: α ↪⊔ β) (g: β ↪⊔ γ) : α ↪⊔ γ := {
  g.toMaxHom.comp f.toMaxHom, f.toEmbedding.trans g.toEmbedding with
}
def LatticeEmbedding.trans (f: α ↪⊓⊔ β) (g: β ↪⊓⊔ γ) : α ↪⊓⊔ γ := {
  f.toMinEmbedding.trans g.toMinEmbedding, f.toMaxEmbedding.trans g.toMaxEmbedding with
}
def OrderEmbedding.trans (f: α ↪o β) (g: β ↪o γ) : α ↪o γ := {
  f.toEmbedding.trans g.toEmbedding, g.toOrderHom.comp f.toOrderHom with
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
def OrderEquiv.trans (f: α ≃o β) (g: β ≃o γ) : α ≃o γ := {
  f.toEquiv.trans g.toEquiv, g.toOrderHom.comp f.toOrderHom with
}

@[symm] def MinEquiv.symm (f: α ≃⊓ β) : β ≃⊓ α := {
  f.toEquiv.symm with
  map_min a b := by
    simp
    apply f.inj
    show _ = f _
    rw [map_min f, f.symm_coe]
    symm; congr <;> apply Equiv.symm_coe
}
@[symm] def MaxEquiv.symm (f: α ≃⊔ β) : β ≃⊔ α := {
  f.toEquiv.symm with
  map_max a b := by
    simp
    apply f.inj
    show _ = f _
    rw [map_max f, f.symm_coe]
    symm; congr <;> apply Equiv.symm_coe
}
@[symm] def LatticeEquiv.symm (f: α ≃⊓⊔ β) : β ≃⊓⊔ α := {
  f.toMinEquiv.symm, f.toMaxEquiv.symm with
}
@[symm] def OrderEquiv.symm (f: α ≃o β) : β ≃o α := {
  f.toEquiv.symm with
  map_le a b := by
    simp; apply Iff.trans _ (f.map_le _ _).symm
    simp
}

def MinEmbedding.toHom (f: α ↪⊓ β) : α →⊓ β := { f with }
def MaxEmbedding.toHom (f: α ↪⊔ β) : α →⊔ β := { f with }
def LatticeEmbedding.toHom (f: α ↪⊓⊔ β) : α →⊓⊔ β := { f with }
def OrderEmbedding.toHom (f: α ↪o β) : α →o β := { f with }
def MinEquiv.toEmbedding (f: α ≃⊓ β) : α ↪⊓ β := { f, f.toEquiv.toEmbedding with }
def MaxEquiv.toEmbedding (f: α ≃⊔ β) : α ↪⊔ β := { f, f.toEquiv.toEmbedding with }
def LatticeEquiv.toEmbedding (f: α ≃⊓⊔ β) : α ↪⊓⊔ β := { f, f.toEquiv.toEmbedding with }
def OrderEquiv.toEmbedding (f: α ≃o β) : α ↪o β := { f, f.toEquiv.toEmbedding with }
def MinEquiv.toHom (f: α ≃⊓ β) : α →⊓ β := { f with }
def MaxEquiv.toHom (f: α ≃⊔ β) : α →⊔ β := { f with }
def LatticeEquiv.toHom (f: α ≃⊓⊔ β) : α →⊓⊔ β := { f with }
def OrderEquiv.toHom (f: α ≃o β) : α →o β := { f with }

def MinEmbedding.inj (f: α ↪⊓ β) : Function.Injective f := f.toEmbedding.inj
def MaxEmbedding.inj (f: α ↪⊔ β) : Function.Injective f := f.toEmbedding.inj
def LatticeEmbedding.inj (f: α ↪⊓⊔ β) : Function.Injective f := f.toEmbedding.inj
def OrderEmbedding.inj (f: α ↪o β) : Function.Injective f := f.toEmbedding.inj
def MinEquiv.inj (f: α ≃⊓ β) : Function.Injective f := f.toEmbedding.inj
def MaxEquiv.inj (f: α ≃⊔ β) : Function.Injective f := f.toEmbedding.inj
def LatticeEquiv.inj (f: α ≃⊓⊔ β) : Function.Injective f := f.toEmbedding.inj
def OrderEquiv.inj (f: α ≃o β) : Function.Injective f := f.toEmbedding.inj

def MinHom.ext (f g: α →⊓ α) : (∀x, f x = g x ) -> f = g := DFunLike.ext _ _
def MaxHom.ext (f g: α →⊔ α) : (∀x, f x = g x ) -> f = g := DFunLike.ext _ _
def LatticeHom.ext (f g: α →⊓⊔ α) : (∀x, f x = g x ) -> f = g := DFunLike.ext _ _
def MonotoneHom.ext (f g: α →≤ α) : (∀x, f x = g x ) -> f = g := DFunLike.ext _ _
def StrictMonotoneHom.ext (f g: α →< α) : (∀x, f x = g x ) -> f = g := DFunLike.ext _ _
def OrderHom.ext (f g: α →o α) : (∀x, f x = g x ) -> f = g := DFunLike.ext _ _
def MinEmbedding.ext (f g: α ↪⊓ α) : (∀x, f x = g x ) -> f = g := DFunLike.ext _ _
def MaxEmbedding.ext (f g: α ↪⊔ α) : (∀x, f x = g x ) -> f = g := DFunLike.ext _ _
def LatticeEmbedding.ext (f g: α ↪⊓⊔ α) : (∀x, f x = g x ) -> f = g := DFunLike.ext _ _
def OrderEmbedding.ext (f g: α ↪o α) : (∀x, f x = g x ) -> f = g := DFunLike.ext _ _
def MinEquiv.ext (f g: α ≃⊓ α) : (∀x, f x = g x ) -> f = g := DFunLike.ext _ _
def MaxEquiv.ext (f g: α ≃⊔ α) : (∀x, f x = g x ) -> f = g := DFunLike.ext _ _
def LatticeEquiv.ext (f g: α ≃⊓⊔ α) : (∀x, f x = g x ) -> f = g := DFunLike.ext _ _
def OrderEquiv.ext (f g: α ≃o α) : (∀x, f x = g x ) -> f = g := DFunLike.ext _ _

@[simp] def MinEquiv.trans_symm (f: α ≃⊓ β) : f.trans f.symm = .refl _ := by hom_equiv_trans_symm_impl f
@[simp] def MaxEquiv.trans_symm (f: α ≃⊔ β) : f.trans f.symm = .refl _ := by hom_equiv_trans_symm_impl f
@[simp] def LatticeEquiv.trans_symm (f: α ≃⊓⊔ β) : f.trans f.symm = .refl _ := by hom_equiv_trans_symm_impl f
@[simp] def OrderEquiv.trans_symm (f: α ≃o β) : f.trans f.symm = .refl _ := by hom_equiv_trans_symm_impl f

@[simp] def MinEquiv.symm_trans (f: α ≃⊓ β) : f.symm.trans f = .refl _ := by hom_equiv_trans_symm_impl f
@[simp] def MaxEquiv.symm_trans (f: α ≃⊔ β) : f.symm.trans f = .refl _ := by hom_equiv_trans_symm_impl f
@[simp] def LatticeEquiv.symm_trans (f: α ≃⊓⊔ β) : f.symm.trans f = .refl _ := by hom_equiv_trans_symm_impl f
@[simp] def OrderEquiv.symm_trans (f: α ≃o β) : f.symm.trans f = .refl _ := by hom_equiv_trans_symm_impl f

@[simp] def MinEquiv.symm_symm (f: α ≃⊓ β) : f.symm.symm = f := by apply EquivLike.coe_inj; apply Equiv.symm_symm
@[simp] def MaxEquiv.symm_symm (f: α ≃⊔ β) : f.symm.symm = f := by apply EquivLike.coe_inj; apply Equiv.symm_symm
@[simp] def LatticeEquiv.symm_symm (f: α ≃⊓⊔ β) : f.symm.symm = f := by apply EquivLike.coe_inj; apply Equiv.symm_symm
@[simp] def OrderEquiv.symm_symm (f: α ≃o β) : f.symm.symm = f := by apply EquivLike.coe_inj; apply Equiv.symm_symm

@[simp] def MinEquiv.coe_symm (f: α ≃⊓ β) (x: α) : f.symm (f x) = x := Equiv.coe_symm _ _
@[simp] def MaxEquiv.coe_symm (f: α ≃⊔ β) (x: α) : f.symm (f x) = x := Equiv.coe_symm _ _
@[simp] def LatticeEquiv.coe_symm (f: α ≃⊓⊔ β) (x: α) : f.symm (f x) = x := Equiv.coe_symm _ _
@[simp] def OrderEquiv.coe_symm (f: α ≃o β) (x: α) : f.symm (f x) = x := Equiv.coe_symm _ _

@[simp] def MinEquiv.symm_coe (f: α ≃⊓ β) (x: β) : f (f.symm x) = x := Equiv.symm_coe _ _
@[simp] def MaxEquiv.symm_coe (f: α ≃⊔ β) (x: β) : f (f.symm x) = x := Equiv.symm_coe _ _
@[simp] def LatticeEquiv.symm_coe (f: α ≃⊓⊔ β) (x: β) : f (f.symm x) = x := Equiv.symm_coe _ _
@[simp] def OrderEquiv.symm_coe (f: α ≃o β) (x: β) : f (f.symm x) = x := Equiv.symm_coe _ _

@[simp] def MinEquiv.toEquiv_eq_coe (f: α ≃⊓ β) : f.toEquiv = (f: _ -> _) := rfl
@[simp] def MaxEquiv.toEquiv_eq_coe (f: α ≃⊔ β) : f.toEquiv = (f: _ -> _) := rfl
@[simp] def LatticeEquiv.toEquiv_eq_coe (f: α ≃⊓⊔ β) : f.toEquiv = (f: _ -> _) := rfl
@[simp] def OrderEquiv.toEquiv_eq_coe (f: α ≃o β) : f.toEquiv = (f: _ -> _) := rfl
