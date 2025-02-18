import Math.Algebra.Hom.Defs
import Math.Algebra.Module.Defs

variable [SMul R A] [SMul R B] [SMul R C]

structure LinearMap (R A B: Type*) [Add A] [Add B] [SMul R A] [SMul R B] extends AddHom A B, SMulHom R A B where

notation:25 A " →ₗ[" R "] " B => LinearMap R A B

structure LinearEmbedding (R A B: Type*) [Add A] [Add B] [SMul R A] [SMul R B] extends A ↪ B, A →ₗ[R] B where

notation:25 A " ↪ₗ[" R "] " B => LinearEmbedding R A B

structure LinearEquiv (R A B: Type*) [Add A] [Add B] [SMul R A] [SMul R B] extends A ≃ B, A →ₗ[R] B where

notation:25 A " ≃ₗ[" R "] " B => LinearEquiv R A B

instance [Add A] [Add B] : FunLike (A →ₗ[R] B) A B where
  coe f := f.toFun
  coe_inj := by
    intro f g eq; cases f; cases g; congr
    apply DFunLike.coe_inj
    assumption

instance [Add A] [Add B] : IsAddHom (A →ₗ[R] B) A B where
  resp_add f := f.resp_add
instance [Add A] [Add B] : IsSMulHom (A →ₗ[R] B) R A B where
  resp_smul f := f.resp_smul
instance
  [AddMonoidOps A] [AddMonoidOps B] [SemiringOps R]
  [IsAddMonoid A] [IsAddMonoid B] [IsAddCommMagma B] [IsSemiring R]
  [IsDistribMulAction R A] [IsModule R B] : IsZeroHom (A →ₗ[R] B) A B where
  resp_zero := by
    intro f
    rw [←smul_zero (0: R), resp_smul, zero_smul]

instance [Add A] [Add B] : FunLike (A ↪ₗ[R] B) A B where
  coe f := f.toFun
  coe_inj := by
    intro f g eq; cases f; cases g; congr
    apply DFunLike.coe_inj
    assumption

instance [Add A] [Add B] : IsAddHom (A ↪ₗ[R] B) A B where
  resp_add f := f.resp_add
instance [Add A] [Add B] : IsSMulHom (A ↪ₗ[R] B) R A B where
  resp_smul f := f.resp_smul
instance
  [AddMonoidOps A] [AddMonoidOps B] [SemiringOps R]
  [IsAddMonoid A] [IsAddMonoid B] [IsAddCommMagma B] [IsSemiring R]
  [IsDistribMulAction R A] [IsModule R B] : IsZeroHom (A ↪ₗ[R] B) A B where
  resp_zero := by
    intro f
    rw [←smul_zero (0: R), resp_smul, zero_smul]

def LinearEmbedding.refl (R A: Type*) [Add A] [SMul R A] : A ↪ₗ[R] A where
  toEmbedding := .refl
  resp_add := rfl
  resp_smul := rfl

def LinearEmbedding.trans {R A B C: Type*} [Add A] [Add B] [Add C] [SMul R A] [SMul R B] [SMul R C] (h: A ↪ₗ[R] B) (g: B ↪ₗ[R] C) : A ↪ₗ[R] C where
  toEmbedding := h.toEmbedding.trans g.toEmbedding
  resp_add := by
    intro a b
    apply flip Eq.trans
    apply g.resp_add
    show g _ = g _
    congr
    apply h.resp_add
  resp_smul := by
    intro a b
    apply flip Eq.trans
    apply g.resp_smul
    show g _ = g _
    congr
    apply h.resp_smul

instance [Add A] [Add B] : FunLike (A ≃ₗ[R] B) A B where
  coe f := f.toFun
  coe_inj := by
    intro f g eq; cases f; cases g; congr
    apply DFunLike.coe_inj
    assumption

instance [Add A] [Add B] : IsAddHom (A ≃ₗ[R] B) A B where
  resp_add f := f.resp_add
instance [Add A] [Add B] : IsSMulHom (A ≃ₗ[R] B) R A B where
  resp_smul f := f.resp_smul
instance
  [AddMonoidOps A] [AddMonoidOps B] [SemiringOps R]
  [IsAddMonoid A] [IsAddMonoid B] [IsAddCommMagma B] [IsSemiring R]
  [IsDistribMulAction R A] [IsModule R B] : IsZeroHom (A ≃ₗ[R] B) A B where
  resp_zero := by
    intro f
    rw [←smul_zero (0: R), resp_smul, zero_smul]

def LinearEquiv.refl (R A: Type*) [Add A] [SMul R A] : A ≃ₗ[R] A where
  toEquiv := .refl
  resp_add := rfl
  resp_smul := rfl

def LinearEquiv.symm {R A B: Type*} [Add A] [Add B] [SMul R A] [SMul R B] (h: A ≃ₗ[R] B) : B ≃ₗ[R] A where
  toEquiv := h.toEquiv.symm
  resp_add := by
    intro a b
    rw [←h.coe_symm (_ + _)]
    congr
    show _ = h (h.toEquiv.symm _ + h.toEquiv.symm _)
    rw [IsAddHom.resp_add]
    congr
    apply (h.symm_coe _).symm
    apply (h.symm_coe _).symm
  resp_smul := by
    intro r x
    apply h.inj
    show h.toEquiv (h.toEquiv.symm _) = h.toFun (_ • h.invFun _)
    rw [h.symm_coe, h.resp_smul, h.rightInv]

def LinearEquiv.trans {R A B C: Type*} [Add A] [Add B] [Add C] [SMul R A] [SMul R B] [SMul R C] (h: A ≃ₗ[R] B) (g: B ≃ₗ[R] C) : A ≃ₗ[R] C where
  toEquiv := h.toEquiv.trans g.toEquiv
  resp_add := by
    intro a b
    apply flip Eq.trans
    apply g.resp_add
    show g _ = g _
    congr
    apply h.resp_add
  resp_smul := by
    intro a b
    apply flip Eq.trans
    apply g.resp_smul
    show g _ = g _
    congr
    apply h.resp_smul

def toLinearMap
  [FunLike F A B] [SMul R A] [SMul R B] [Add A] [Add B]
  [IsAddHom F A B] [IsSMulHom F R A B] (f: F) : LinearMap R A B where
  toFun := f
  resp_add := resp_add _
  resp_smul := resp_smul _

def LinearMap.comp [Add A] [Add B] [Add C] (f: B →ₗ[R] C) (g: A →ₗ[R] B) : A →ₗ[R] C where
  toFun := f.toFun ∘ g.toFun
  resp_add { _ _ } := by dsimp; rw [g.resp_add, f.resp_add]
  resp_smul { _ _ } := by dsimp; rw [g.resp_smul, f.resp_smul]

def LinearMap.id (A: Type*) [Add A] [SMul R A] : A →ₗ[R] A where
  toFun x := x
  resp_add := rfl
  resp_smul := rfl

instance
  [Add A] [AddMonoidOps B] [MonoidOps R]
  [IsAddMonoid B] [IsAddCommMagma B]
  [IsMonoid R] [IsDistribMulAction R B]
  : Add (A →ₗ[R] B) where
  add f g := {
    toFun x := f x + g x
    resp_add := by
      intro x y
      dsimp
      rw [resp_add, resp_add]
      rw [←add_assoc, add_assoc (f x), add_comm (f y), ←add_assoc, add_assoc]
    resp_smul := by
      intro r x
      dsimp
      rw [resp_smul, resp_smul, smul_add]
  }

instance
  [Add A] [AddMonoidOps B] [MonoidOps R]
  [IsMonoid R] [IsAddMonoid B]
  [IsSMulComm R R B] [IsDistribMulAction R B]
  : SMul R (A →ₗ[R] B) where
  smul r f := {
    toFun x := r • f x
    resp_add := by
      intro x y; dsimp
      rw [resp_add, smul_add]
    resp_smul := by
      intro r x
      dsimp
      rw [resp_smul, smul_comm]
  }

/-- A shorthand for the type of `R`-bilinear `Nₗ`-valued maps on `M`. -/
abbrev BilinMap
  (R A B: Type*)
  [Add A] [AddMonoidOps B] [MonoidOps R]
  [IsMonoid R] [IsCommMagma R]
  [IsAddMonoid B] [IsAddCommMagma B]
  [SMul R A] [SMul R B] [IsDistribMulAction R B]
  : Type _ := A →ₗ[R] A →ₗ[R] B
