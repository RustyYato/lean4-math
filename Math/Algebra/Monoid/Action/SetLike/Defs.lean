import Math.Algebra.Monoid.SetLike.Defs

class IsSMulMem (S R: Type*) {M: Type*} [SetLike S M] [SMul R M] where
  protected mem_smul (s: S): ∀r: R, ∀{m}, m ∈ s -> r • m ∈ s

def mem_smul [SetLike S M] [SMul R M] [IsSMulMem S R] (s: S): ∀r: R, ∀{m}, m ∈ s -> r • m ∈ s := IsSMulMem.mem_smul s

structure SubMulAction (M R: Type*) [SMul R M] where
  carrier: Set M
  protected mem_smul: ∀r: R, ∀{m}, m ∈ carrier -> r • m ∈ carrier

instance [SMul R M] : SetLike (SubMulAction M R) M where
  coe s := s.carrier
  coe_inj := by
    intro a b eq; cases a; congr

instance [SMul R M] : IsSMulMem (SubMulAction M R) R where
  mem_smul s := s.mem_smul
