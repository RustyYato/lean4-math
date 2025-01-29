import Math.Algebra.RingHom

variable [SMul R A] [SMul R B] [SMul R C]

structure SMulHom (R A B: Type*) [SMul R A] [SMul R B] where
  toFun: A -> B
  resp_smul: ∀{r: R} {x: A}, toFun (r • x) = r • toFun x

instance : FunLike (SMulHom R A B) A B where
  coe := SMulHom.toFun
  coe_inj := by
    intro f g eq; cases f; congr

class SMulHomClass (F R: Type*) (A B: outParam Type*) [FunLike F A B] [SMul R A] [SMul R B] where
  resp_smul (f: F): ∀{r: R} {x: A}, f (r • x) = r • f x

export SMulHomClass (resp_smul)

instance : SMulHomClass (SMulHom R A B) R A B where
  resp_smul := SMulHom.resp_smul

structure LinearMap (R A B: Type*) [Add A] [Add B] [SMul R A] [SMul R B] extends AddHom A B, SMulHom R A B where

notation:25 A " →ₗ[" R "] " B => LinearMap R A B

instance [Add A] [Add B] : FunLike (A →ₗ[R] B) A B where
  coe f := f.toFun
  coe_inj := by
    intro f g eq; cases f; cases g; congr
    apply DFunLike.coe_inj
    assumption

instance [Add A] [Add B] : AddHomClass (A →ₗ[R] B) A B where
  resp_add f := f.resp_add
instance [Add A] [Add B] : SMulHomClass (A →ₗ[R] B) R A B where
  resp_smul f := f.resp_smul
instance
  [AddMonoidOps A] [AddMonoidOps B] [SemiringOps R]
  [IsAddMonoid A] [IsAddMonoid B] [IsAddCommMagma B] [IsSemiring R]
  [IsDistribMulAction R A] [IsModule R B] : ZeroHomClass (A →ₗ[R] B) A B where
  resp_zero := by
    intro f
    rw [←smul_zero (0: R), resp_smul, zero_smul]

def toLinearMap
  [FunLike F A B] [SMul R A] [SMul R B] [Add A] [Add B]
  [AddHomClass F A B] [SMulHomClass F R A B] (f: F) : LinearMap R A B where
  toFun := f
  resp_add := resp_add _
  resp_smul := resp_smul _

def LinearMap.comp [Add A] [Add B] [Add C] (f: B →ₗ[R] C) (g: A →ₗ[R] B) : A →ₗ[R] C where
  toFun := f.toFun ∘ g.toFun
  resp_add { _ _ } := by dsimp; rw [g.resp_add, f.resp_add]
  resp_smul { _ _ } := by dsimp; rw [g.resp_smul, f.resp_smul]

-- variable
    -- [AddMonoidOps B] [MonoidOps R]
    -- [IsAddMonoid B] [IsMonoid R]
    -- [IsAddCommMagma B] [IsDistribMulAction R B]
    -- [IsSMulComm R R B]

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
  [Add A] [AddMonoidOps B] [MonoidOps R]
  [IsMonoid R] [IsAddMonoid B] [IsAddCommMagma B]
  [IsSMulComm R R B] [IsDistribMulAction R B]
  : Type _ := A →ₗ[R] A →ₗ[R] B
