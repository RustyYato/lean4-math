import Math.Algebra.Ring.Impls.Prod
import Math.Algebra.Module.Impls.Prod
import Math.Algebra.Algebra.Hom

section Prod

variable {α β: Type*}

structure Prod.fstHomType (α β: Type*) where
structure Prod.sndHomType (α β: Type*) where

def Prod.fstHom : Prod.fstHomType α β := fstHomType.mk
def Prod.sndHom : Prod.sndHomType α β := sndHomType.mk

instance : FunLike (Prod.fstHomType (α := α) (β := β)) (α × β) α where
  coe _ := Prod.fst
  coe_inj := by intro a b h; rfl

instance : FunLike (Prod.sndHomType (α := α) (β := β)) (α × β) β where
  coe _ := Prod.snd
  coe_inj := by intro a b h; rfl

instance [Zero α] [Zero β] : IsZeroHom (Prod.fstHomType (α := α) (β := β)) (α × β) α where
  map_zero _ := rfl
instance [Zero α] [Zero β] : IsZeroHom (Prod.sndHomType (α := α) (β := β)) (α × β) β where
  map_zero _ := rfl

instance [One α] [One β] : IsOneHom (Prod.fstHomType (α := α) (β := β)) (α × β) α where
  map_one _ := rfl
instance [One α] [One β] : IsOneHom (Prod.sndHomType (α := α) (β := β)) (α × β) β where
  map_one _ := rfl

instance [Add α] [Add β] : IsAddHom (Prod.fstHomType (α := α) (β := β)) (α × β) α where
  map_add _ := rfl
instance [Add α] [Add β] : IsAddHom (Prod.sndHomType (α := α) (β := β)) (α × β) β where
  map_add _ := rfl

instance [Mul α] [Mul β] : IsMulHom (Prod.fstHomType (α := α) (β := β)) (α × β) α where
  map_mul _ := rfl
instance [Mul α] [Mul β] : IsMulHom (Prod.sndHomType (α := α) (β := β)) (α × β) β where
  map_mul _ := rfl

instance [SMul R α] [SMul R β] : IsSMulHom (Prod.fstHomType (α := α) (β := β)) R (α × β) α where
  map_smul _ := rfl
instance [SMul R α] [SMul R β] : IsSMulHom (Prod.sndHomType (α := α) (β := β)) R (α × β) β where
  map_smul _ := rfl

instance [Subsingleton β] : EmbeddingLike (Prod.fstHomType (α := α) (β := β)) (α × β) α where
  coe h := {
    toFun := h
    inj' := by
      intro a b h
      ext
      assumption
      apply Subsingleton.allEq
  }
  coe_inj := by
    intro f a b
    rfl

instance [Subsingleton α] : EmbeddingLike (Prod.sndHomType (α := α) (β := β)) (α × β) β where
  coe h := {
    toFun := h
    inj' := by
      intro a b h
      ext
      apply Subsingleton.allEq
      assumption
  }
  coe_inj := by
    intro f a b
    rfl

end Prod
