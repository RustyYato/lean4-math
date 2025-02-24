import Math.Algebra.LinearMap

structure QuadraticMap (R M N: Type*)
  [SemiringOps R] [IsSemiring R] [IsCommMagma R]
  [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M]
  [AddMonoidOps N] [IsAddMonoid N] [IsAddCommMagma N]
  [SMul R M] [SMul R N]
  [IsModule R M] [IsModule R N] where
  toFun : M → N
  toFun_smul : ∀ (a : R) (x : M), toFun (a • x) = (a * a) • toFun x
  exists_companion : ∃ B : BilinMap R M N, ∀ x y, toFun (x + y) = toFun x + toFun y + B x y

abbrev QuadraticForm (R M: Type*)
  [SemiringOps R] [IsSemiring R] [IsCommMagma R]
  [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M]
  [SMul R M] [IsModule R M]: Type _ := QuadraticMap R M R

variable
  [SemiringOps R] [IsSemiring R] [IsCommMagma R]
  [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M]
  [AddMonoidOps N] [IsAddMonoid N] [IsAddCommMagma N]
  [SMul R M] [SMul R N]
  [IsModule R M] [IsModule R N]

instance : FunLike (QuadraticMap R M N) M N where
  coe f := f.toFun
  coe_inj := by
    intro a b _; cases a; congr
