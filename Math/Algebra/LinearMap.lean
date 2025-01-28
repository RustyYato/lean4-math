import Math.Algebra.RingHom

variable [SMul R A] [SMul R B] [SMul R C] [Add A] [Add B] [Add C]

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

instance : FunLike (A →ₗ[R] B) A B where
  coe f := f.toFun
  coe_inj := by
    intro f g eq; cases f; cases g; congr
    apply DFunLike.coe_inj
    assumption

instance : AddHomClass (A →ₗ[R] B) A B where
  resp_add f := f.resp_add
instance : SMulHomClass (A →ₗ[R] B) R A B where
  resp_smul f := f.resp_smul
instance
  [Zero R] [Add R] [One R] [Mul R] [SMul ℕ R] [Pow R ℕ] [NatCast R] [∀n, OfNat R (n + 2)] [IsSemiring R]
  [Zero A] [Zero B] [SMul ℕ A] [SMul ℕ B] [IsAddMonoid A] [IsAddMonoid B] [IsAddCommMagma B]
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

def LinearMap.comp (f: B →ₗ[R] C) (g: A →ₗ[R] B) : A →ₗ[R] C where
  toFun := f.toFun ∘ g.toFun
  resp_add { _ _ } := by dsimp; rw [g.resp_add, f.resp_add]
  resp_smul { _ _ } := by dsimp; rw [g.resp_smul, f.resp_smul]

variable [One R] [Mul R] [Pow R ℕ] [IsMonoid R]
    [Zero B] [SMul ℕ B] [IsAddMonoid B]
    [IsAddCommMagma B] [IsDistribMulAction R B]
    [IsSMulComm R R B]

instance : Add (A →ₗ[R] B) where
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

instance : SMul R (A →ₗ[R] B) where
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

variable [IsAddCommMagma B] [IsAddSemigroup B]

/-- A shorthand for the type of `R`-bilinear `Nₗ`-valued maps on `M`. -/
abbrev BilinMap : Type _ := A →ₗ[R] A →ₗ[R] B
