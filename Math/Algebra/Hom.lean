import Math.Algebra.Hom.Defs
import Math.Algebra.LinearMap
import Math.Algebra.Basic
import Math.Data.Like.Embedding
import Math.Logic.Equiv.Like

section

variable (F R A B: Type*)
  [FunLike F A B]
  [SemiringOps R] [SemiringOps A] [SemiringOps B] [SemiringOps C]
  [AlgebraMap R A] [AlgebraMap R B] [AlgebraMap R C]

structure AlgebraMapHom where
  toFun: A -> B
  resp_algebraMap : ∀r: R, toFun (algebraMap r: A) = (algebraMap r: B)

notation:25 A " →ₐ₀[" R "] " B => AlgebraMapHom R A B

class IsAlgebraMapHom where
  resp_algebraMap (f: F) : ∀r: R, f (algebraMap r: A) = (algebraMap r: B)

export IsAlgebraMapHom (resp_algebraMap)

structure AlgHom extends A →+* B where
  resp_algebraMap : ∀r: R, toFun (algebraMap r: A) = (algebraMap r: B)

notation:25 A " →ₐ[" R "] " B => AlgHom R A B

instance : FunLike (A →ₐ[R] B) A B where
  coe f := f.toFun
  coe_inj := by
    intro x y eq
    cases x; cases y
    congr
    apply DFunLike.coe_inj eq

instance : IsZeroHom (A →ₐ[R] B) A B where
  resp_zero f := f.resp_zero

instance : IsOneHom (A →ₐ[R] B) A B where
  resp_one f := f.resp_one

instance : IsAddHom (A →ₐ[R] B) A B where
  resp_add f := f.resp_add

instance : IsMulHom (A →ₐ[R] B) A B where
  resp_mul f := f.resp_mul

instance : IsAlgebraMapHom (A →ₐ[R] B) R A B where
  resp_algebraMap f := f.resp_algebraMap

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

instance : IsEmbeddingLike (A ↪ₐ[R] B) A B where
  coe_inj f := f.inj

instance : IsZeroHom (A ↪ₐ[R] B) A B where
  resp_zero f := f.resp_zero

instance : IsOneHom (A ↪ₐ[R] B) A B where
  resp_one f := f.resp_one

instance : IsAddHom (A ↪ₐ[R] B) A B where
  resp_add f := f.resp_add

instance : IsMulHom (A ↪ₐ[R] B) A B where
  resp_mul f := f.resp_mul

instance : IsAlgebraMapHom (A ↪ₐ[R] B) R A B where
  resp_algebraMap f := f.resp_algebraMap

instance : EquivLike (A ≃ₐ[R] B) A B where
  coe := AlgEquiv.toEquiv
  coe_inj := by
    intro a b eq; cases a
    congr

instance : IsZeroHom (A ≃ₐ[R] B) A B where
  resp_zero f := f.resp_zero

instance : IsOneHom (A ≃ₐ[R] B) A B where
  resp_one f := f.resp_one

instance : IsAddHom (A ≃ₐ[R] B) A B where
  resp_add f := f.resp_add

instance : IsMulHom (A ≃ₐ[R] B) A B where
  resp_mul f := f.resp_mul

instance : IsAlgebraMapHom (A ≃ₐ[R] B) R A B where
  resp_algebraMap f := f.resp_algebraMap

end

section

variable {F R A B: Type*}
  [FunLike F A B]
  [SemiringOps R] [SemiringOps A] [SemiringOps B] [SemiringOps C]
  [AlgebraMap R A] [AlgebraMap R B] [AlgebraMap R C]
variable [IsZeroHom F A B] [IsOneHom F A B] [IsAddHom F A B] [IsMulHom F A B]
   [IsAlgebraMapHom F R A B]

@[coe]
def toAlgebraMapHom (f: F) : A →ₐ₀[R] B where
  toFun := f
  resp_algebraMap := resp_algebraMap f

@[coe]
def toAlgHom' (f: F) : A →ₐ[R] B where
  toRingHom := toRingHom f
  resp_algebraMap := resp_algebraMap f

instance [SMul R A] [SMul R B] [IsSemiring A] [IsSemiring B] [IsAlgebra R A] [IsAlgebra R B]: IsSMulHom F R A B where
  resp_smul := by
    intro f r x
    rw [smul_def, smul_def, resp_mul, resp_algebraMap]

end

section

variable (F R A B: Type*)
  [FunLike F A B]
  [SemiringOps R] [SemiringOps A] [SemiringOps B] [SemiringOps C]
  [AlgebraMap R A] [AlgebraMap R B] [AlgebraMap R C]

variable [IsAddHom F A B] [IsMulHom F A B] [IsAlgebraMapHom F R A B]
  [SMul R A] [SMul R B] [IsSemiring A] [IsSemiring B] [IsAlgebra R A] [IsAlgebra R B]

def toAlgHom (f: F) : A →ₐ[R] B where
  toFun := f
  resp_algebraMap := resp_algebraMap f
  resp_mul := resp_mul f
  resp_add := resp_add f
  resp_zero := by rw [←resp_zero (algebraMap (R := R)), resp_algebraMap, resp_zero]
  resp_one := by
    dsimp
    rw [←resp_one (algebraMap (R := R)), resp_algebraMap, resp_one]

end

section

variable {R A B C: Type*}
  [FunLike F A B]
  [SemiringOps R] [SemiringOps A] [SemiringOps B] [SemiringOps C]
  [AlgebraMap R A] [AlgebraMap R B] [AlgebraMap R C]

def AlgHom.toLinearMap
  [SMul R A] [SMul R B]
  [IsSemiring R] [IsSemiring A] [IsSemiring B]
  [IsAlgebra R A] [IsAlgebra R B]
  (h: A →ₐ[R] B) : A →ₗ[R] B where
  toFun := h
  resp_add := resp_add h
  resp_smul := resp_smul h

def AlgHom.comp (h: B →ₐ[R] C) (g: A →ₐ[R] B) : A →ₐ[R] C where
  toFun := h.toFun ∘ g.toFun
  resp_zero := by
    dsimp
    rw [g.resp_zero, h.resp_zero]
  resp_one := by
    dsimp
    rw [g.resp_one, h.resp_one]
  resp_add {_ _} := by
    dsimp
    rw [g.resp_add, h.resp_add]
  resp_mul {_ _} := by
    dsimp
    rw [g.resp_mul, h.resp_mul]
  resp_algebraMap {_} := by
    dsimp
    rw [g.resp_algebraMap, h.resp_algebraMap]

def AlgEmbedding.comp (h: B ↪ₐ[R] C) (g: A ↪ₐ[R] B) : A ↪ₐ[R] C where
  toEmbedding := (g.toEmbedding.trans h.toEmbedding)
  -- inj := (g.toEmbedding.trans h.toEmbedding).inj
  resp_zero := by
    dsimp [Embedding.trans, DFunLike.coe]
    rw [resp_zero, resp_zero]
  resp_one := by
    dsimp [Embedding.trans, DFunLike.coe]
    rw [g.resp_one, h.resp_one]
  resp_add {_ _} := by
    dsimp [Embedding.trans, DFunLike.coe]
    rw [g.resp_add, h.resp_add]
  resp_mul {_ _} := by
    dsimp [Embedding.trans, DFunLike.coe]
    rw [g.resp_mul, h.resp_mul]
  resp_algebraMap {_} := by
    show h.toFun (g.toFun _) = _
    rw [g.resp_algebraMap, h.resp_algebraMap]

def AlgEquiv.comp (h: B ≃ₐ[R] C) (g: A ≃ₐ[R] B) : A ≃ₐ[R] C where
  toEquiv := g.toEquiv.trans h.toEquiv
  resp_zero := by
    dsimp [Equiv.trans]
    rw [g.resp_zero, h.resp_zero]
  resp_one := by
    dsimp [Equiv.trans]
    rw [g.resp_one, h.resp_one]
  resp_add {_ _} := by
    dsimp [Equiv.trans]
    rw [g.resp_add, h.resp_add]
  resp_mul {_ _} := by
    dsimp [Equiv.trans]
    rw [g.resp_mul, h.resp_mul]
  resp_algebraMap {_} := by
    dsimp [Equiv.trans]
    rw [g.resp_algebraMap, h.resp_algebraMap]

def AlgEmbedding.trans (h: A ↪ₐ[R] B) (g: B ↪ₐ[R] C) : A ↪ₐ[R] C := g.comp h
def AlgEquiv.trans (h: A ≃ₐ[R] B) (g: B ≃ₐ[R] C) : A ≃ₐ[R] C := g.comp h

def AlgEmbedding.refl : A ↪ₐ[R] A where
  toEmbedding := .rfl
  resp_zero := rfl
  resp_one := rfl
  resp_add := rfl
  resp_mul := rfl
  resp_algebraMap _ := rfl

def AlgEquiv.refl : A ≃ₐ[R] A where
  toEquiv := .rfl
  resp_zero := rfl
  resp_one := rfl
  resp_add := rfl
  resp_mul := rfl
  resp_algebraMap _ := rfl

def AlgEquiv.symm (h: A ≃ₐ[R] B) : B ≃ₐ[R] A where
  toEquiv := h.toEquiv.symm
  resp_zero := by
    rw [←h.coe_symm 0]
    show h.toEquiv.symm 0 = h.toEquiv.symm (h.toFun 0)
    rw [h.resp_zero]
  resp_one := by
    rw [←h.coe_symm 1]
    show h.toEquiv.symm 1 = h.toEquiv.symm (h.toFun 1)
    rw [h.resp_one]
  resp_add {a b} := by
    rw [←h.coe_symm (_ + _)]
    show h.toEquiv.symm _ = h.toEquiv.symm (h.toFun _)
    erw [h.resp_add, h.rightInv, h.rightInv]
  resp_mul {a b} := by
    rw [←h.coe_symm (_ * _)]
    show h.toEquiv.symm _ = h.toEquiv.symm (h.toFun _)
    erw [h.resp_mul, h.rightInv, h.rightInv]
  resp_algebraMap x := by
    rw [←h.coe_symm (algebraMap x)]
    show h.toEquiv.symm (algebraMap x) = h.toEquiv.symm (h.toFun (algebraMap x))
    rw [h.resp_algebraMap]

end
