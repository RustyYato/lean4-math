import Math.Algebra.Monoid.Action.SetLike.Defs

structure SubModule (R M: Type*) [Zero M] [Add M] [SMul R M] extends SubAddMonoid M,  SubMulAction M R where

variable [Zero M] [Add M] [SMul R M]

instance : SetLike (SubModule R M) M where
  coe s := s.carrier
  coe_inj := by
    intro a b eq; cases a; congr
    apply SetLike.coe_inj
    assumption

instance : IsSubAddMonoid (SubModule R M) where
  mem_zero s := s.mem_zero'
  mem_add s := s.mem_add'

instance : IsSMulMem (SubModule R M) R where
  mem_smul s := s.mem_smul'
