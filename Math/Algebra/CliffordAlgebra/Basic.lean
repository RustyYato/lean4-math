import Math.Algebra.CliffordAlgebra.Defs
import Math.Algebra.Monoid.Units.Defs

namespace CliffordAlgebra

variable [SemiringOps R] [IsSemiring R] [IsCommMagma R] [AddMonoidOps V]
  [IsAddMonoid V] [IsAddCommMagma V] [SMul R V] [IsModule R V]

variable (Q: QuadraticForm R V)

inductive IsVersor : CliffordAlgebra Q -> Prop where
| scalar (x: R) : IsUnit x -> IsVersor (algebraMap x)
| mul_vec (x: CliffordAlgebra Q) (v: V) : IsVersor x -> IsUnit (ι Q v) -> IsVersor (x * ι Q v)

-- every versor is invertible
def IsVersor.toIsUnit (x: CliffordAlgebra Q) (h: x.IsVersor) : IsUnit x := by
  induction h with
  | scalar x hx =>
    obtain ⟨⟨x, inv, xinv, invx⟩ , rfl⟩ := hx
    refine ⟨⟨_, algebraMap inv, ?_, ?_⟩, rfl⟩
    rw [←resp_mul, xinv, resp_one]
    rw [←resp_mul, invx, resp_one]
  | mul_vec x v _ hv hx =>
    obtain ⟨⟨x, x', xinv, invx⟩ , rfl⟩ := hx
    obtain ⟨⟨v, v', vinv, invv⟩ , rfl⟩ := hv
    refine ⟨⟨_, v' * x', ?_, ?_⟩, rfl⟩
    simp
    rw [mul_assoc, ←mul_assoc _ v', vinv, one_mul, xinv]
    rw [mul_assoc, ←mul_assoc x', invx, one_mul, invv]

end CliffordAlgebra
