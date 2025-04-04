import Math.Algebra.Hom.Defs
import Math.Algebra.Module.LinearMap.Defs
import Math.Algebra.Algebra.Defs
import Math.Logic.Equiv.Like

section

variable (F R A B: Type*)
  [FunLike F A B]
  [SemiringOps R] [SemiringOps A] [SemiringOps B] [SemiringOps C]
  [AlgebraMap R A] [AlgebraMap R B] [AlgebraMap R C]

structure AlgebraMapHom where
  toFun: A -> B
  protected map_algebraMap : ∀r: R, toFun (algebraMap r: A) = (algebraMap r: B)

notation:25 A " →ₐ₀[" R "] " B => AlgebraMapHom R A B

class IsAlgebraMapHom where
  protected map_algebraMap (f: F) : ∀r: R, f (algebraMap r: A) = (algebraMap r: B)

structure AlgHom extends A →+* B, A →ₐ₀[R] B where

notation:25 A " →ₐ[" R "] " B => AlgHom R A B

instance : FunLike (A →ₐ[R] B) A B where
  coe f := f.toFun
  coe_inj := by
    intro x y eq
    cases x; cases y
    congr
    apply DFunLike.coe_inj eq

instance : IsZeroHom (A →ₐ[R] B) A B where
  map_zero f := f.map_zero

instance : IsOneHom (A →ₐ[R] B) A B where
  map_one f := f.map_one

instance : IsAddHom (A →ₐ[R] B) A B where
  map_add f := f.map_add

instance : IsMulHom (A →ₐ[R] B) A B where
  map_mul f := f.map_mul

instance : IsAlgebraMapHom (A →ₐ[R] B) R A B where
  map_algebraMap f := f.map_algebraMap

structure AlgEmbedding extends A ↪ B, A →ₐ[R] B where

notation:25 A " ↪ₐ[" R "] " B => AlgEmbedding R A B

structure AlgEquiv extends A ≃ B, A →ₐ[R] B where

notation:25 A " ≃ₐ[" R "] " B => AlgEquiv R A B

instance : FunLike (A ↪ₐ[R] B) A B where
  coe f := f.toFun
  coe_inj := by
    intro x y eq
    cases x; cases y
    congr
    apply DFunLike.coe_inj eq

instance : EmbeddingLike (A ↪ₐ[R] B) A B where
  coe h := h.toEmbedding
  coe_inj := by intro a b h; cases a; congr


instance : IsZeroHom (A ↪ₐ[R] B) A B where
  map_zero f := f.map_zero

instance : IsOneHom (A ↪ₐ[R] B) A B where
  map_one f := f.map_one

instance : IsAddHom (A ↪ₐ[R] B) A B where
  map_add f := f.map_add

instance : IsMulHom (A ↪ₐ[R] B) A B where
  map_mul f := f.map_mul

instance : IsAlgebraMapHom (A ↪ₐ[R] B) R A B where
  map_algebraMap f := f.map_algebraMap

instance : EquivLike (A ≃ₐ[R] B) A B where
  coe := AlgEquiv.toEquiv
  coe_inj := by
    intro a b eq; cases a
    congr

instance : IsZeroHom (A ≃ₐ[R] B) A B where
  map_zero f := f.map_zero

instance : IsOneHom (A ≃ₐ[R] B) A B where
  map_one f := f.map_one

instance : IsAddHom (A ≃ₐ[R] B) A B where
  map_add f := f.map_add

instance : IsMulHom (A ≃ₐ[R] B) A B where
  map_mul f := f.map_mul

instance : IsAlgebraMapHom (A ≃ₐ[R] B) R A B where
  map_algebraMap f := f.map_algebraMap

end

section

variable {F R A B: Type*}
  [FunLike F A B]
  [SemiringOps R] [SemiringOps A] [SemiringOps B] [SemiringOps C]
  [AlgebraMap R A] [AlgebraMap R B] [AlgebraMap R C]
variable [IsZeroHom F A B] [IsOneHom F A B] [IsAddHom F A B] [IsMulHom F A B]
   [IsAlgebraMapHom F R A B]

def map_algebraMap (f: F) : ∀r: R, f (algebraMap r: A) = (algebraMap r: B) :=
  IsAlgebraMapHom.map_algebraMap f

@[coe]
def toAlgebraMapHom (f: F) : A →ₐ₀[R] B where
  toFun := f
  map_algebraMap := map_algebraMap f

@[coe]
def toAlgHom' (f: F) : A →ₐ[R] B where
  toRingHom := toRingHom f
  map_algebraMap := map_algebraMap f

instance [SMul R A] [SMul R B] [IsSemiring A] [IsSemiring B] [IsSemiring R] [IsAlgebra R A] [IsAlgebra R B]: IsSMulHom F R A B where
  map_smul := by
    intro f r x
    rw [smul_def, smul_def, map_mul, map_algebraMap]

end

section

variable (F R A B: Type*)
  [FunLike F A B]
  [SemiringOps R] [SemiringOps A] [SemiringOps B] [SemiringOps C]
  [AlgebraMap R A] [AlgebraMap R B] [AlgebraMap R C]

variable [IsAddHom F A B] [IsMulHom F A B] [IsAlgebraMapHom F R A B]
  [SMul R A] [SMul R B] [IsSemiring A] [IsSemiring B] [IsSemiring R] [IsAlgebra R A] [IsAlgebra R B]

def toAlgHom (f: F) : A →ₐ[R] B where
  toFun := f
  map_algebraMap := map_algebraMap f
  map_mul := map_mul f
  map_add := map_add f
  map_zero := by rw [←map_zero (algebraMap (R := R)), map_algebraMap, map_zero]
  map_one := by
    dsimp
    rw [←map_one (algebraMap (R := R)), map_algebraMap, map_one]

end

section

variable {R A B C: Type*}
  [FunLike F A B]
  [SemiringOps R] [SemiringOps A] [SemiringOps B] [SemiringOps C]
  [AlgebraMap R A] [AlgebraMap R B] [AlgebraMap R C]

@[ext]
def AlgHom.ext (f g: A →ₐ[R] B) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _

def AlgHom.toLinearMap
  [SMul R A] [SMul R B]
  [IsSemiring R] [IsSemiring A] [IsSemiring B]
  [IsAlgebra R A] [IsAlgebra R B]
  (h: A →ₐ[R] B) : A →ₗ[R] B where
  toFun := h
  map_add := map_add h
  map_smul := map_smul h

def AlgHom.comp (h: B →ₐ[R] C) (g: A →ₐ[R] B) : A →ₐ[R] C where
  toFun := h.toFun ∘ g.toFun
  map_zero := by
    dsimp
    rw [g.map_zero, h.map_zero]
  map_one := by
    dsimp
    rw [g.map_one, h.map_one]
  map_add {_ _} := by
    dsimp
    rw [g.map_add, h.map_add]
  map_mul {_ _} := by
    dsimp
    rw [g.map_mul, h.map_mul]
  map_algebraMap {_} := by
    dsimp
    rw [g.map_algebraMap, h.map_algebraMap]

def AlgEmbedding.comp (h: B ↪ₐ[R] C) (g: A ↪ₐ[R] B) : A ↪ₐ[R] C where
  toEmbedding := (g.toEmbedding.trans h.toEmbedding)
  -- inj := (g.toEmbedding.trans h.toEmbedding).inj
  map_zero := by
    show h (g _) = _
    rw [map_zero, map_zero]
  map_one := by
    show h (g _) = _
    rw [map_one, map_one]
  map_add {_ _} := by
    show h (g _) = _
    rw [map_add, map_add]
    rfl
  map_mul {_ _} := by
    show h (g _) = _
    rw [map_mul, map_mul]
    rfl
  map_algebraMap {_} := by
    show h (g _) = _
    rw [map_algebraMap, map_algebraMap]

def AlgEquiv.comp (h: B ≃ₐ[R] C) (g: A ≃ₐ[R] B) : A ≃ₐ[R] C where
  toEquiv := g.toEquiv.trans h.toEquiv
  map_zero := by
    dsimp [Equiv.trans]
    rw [g.map_zero, h.map_zero]
  map_one := by
    dsimp [Equiv.trans]
    rw [g.map_one, h.map_one]
  map_add {_ _} := by
    dsimp [Equiv.trans]
    rw [g.map_add, h.map_add]
  map_mul {_ _} := by
    dsimp [Equiv.trans]
    rw [g.map_mul, h.map_mul]
  map_algebraMap {_} := by
    dsimp [Equiv.trans]
    rw [g.map_algebraMap, h.map_algebraMap]

def AlgEmbedding.trans (h: A ↪ₐ[R] B) (g: B ↪ₐ[R] C) : A ↪ₐ[R] C := g.comp h
def AlgEquiv.trans (h: A ≃ₐ[R] B) (g: B ≃ₐ[R] C) : A ≃ₐ[R] C := g.comp h

def AlgEmbedding.refl : A ↪ₐ[R] A where
  toEmbedding := .rfl
  map_zero := rfl
  map_one := rfl
  map_add := rfl
  map_mul := rfl
  map_algebraMap _ := rfl

def AlgEquiv.refl : A ≃ₐ[R] A where
  toEquiv := .rfl
  map_zero := rfl
  map_one := rfl
  map_add := rfl
  map_mul := rfl
  map_algebraMap _ := rfl

def AlgEquiv.symm (h: A ≃ₐ[R] B) : B ≃ₐ[R] A where
  toEquiv := h.toEquiv.symm
  map_zero := by
    rw [←h.coe_symm 0]
    show h.toEquiv.symm 0 = h.toEquiv.symm (h.toFun 0)
    rw [h.map_zero]
  map_one := by
    rw [←h.coe_symm 1]
    show h.toEquiv.symm 1 = h.toEquiv.symm (h.toFun 1)
    rw [h.map_one]
  map_add {a b} := by
    rw [←h.coe_symm (_ + _)]
    show h.toEquiv.symm _ = h.toEquiv.symm (h.toFun _)
    erw [h.map_add, h.rightInv, h.rightInv]
  map_mul {a b} := by
    rw [←h.coe_symm (_ * _)]
    show h.toEquiv.symm _ = h.toEquiv.symm (h.toFun _)
    erw [h.map_mul, h.rightInv, h.rightInv]
  map_algebraMap x := by
    rw [←h.coe_symm (algebraMap x)]
    show h.toEquiv.symm (algebraMap x) = h.toEquiv.symm (h.toFun (algebraMap x))
    rw [h.map_algebraMap]

end
