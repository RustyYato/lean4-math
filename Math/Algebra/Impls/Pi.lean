import Math.Algebra.Semigroup.Impls.Pi
import Math.Algebra.Hom.Defs

structure Pi.applyHomType {ι: Type*} (α: ι -> Type*) (i: ι) where

variable {ι: Type*} {α: ι -> Type*}

def applyHom (α: ι -> Type*) (i: ι) : Pi.applyHomType α i where

instance : FunLike (Pi.applyHomType α i) (∀i, α i) (α i) where
  coe _ f := f i
  coe_inj := by intro a b h; rfl

instance [∀i, Zero (α i)] : IsZeroHom (Pi.applyHomType α i) (∀i, α i) (α i) where
  map_zero _ := rfl
instance [∀i, One (α i)] : IsOneHom (Pi.applyHomType α i) (∀i, α i) (α i) where
  map_one _ := rfl
instance [∀i, Add (α i)] : IsAddHom (Pi.applyHomType α i) (∀i, α i) (α i) where
  map_add _ := rfl
instance [∀i, Mul (α i)] : IsMulHom (Pi.applyHomType α i) (∀i, α i) (α i) where
  map_mul _ := rfl
instance [∀i, SMul R (α i)] : IsSMulHom (Pi.applyHomType α i) R (∀i, α i) (α i) where
  map_smul _ := rfl

def apply_applyHom (f: ∀i, α i) : applyHom α i f = f i := rfl
