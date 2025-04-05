import Math.Data.Rsqrtd.Basic
import Math.Algebra.Algebra.Defs

namespace Rsqrtd

variable {R: Type*} [SemiringOps R] [IsSemiring R] [IsCommMagma R] {d: R}

instance : AlgebraMap R (R√d) where
  toFun := of
  map_zero := rfl
  map_one := rfl
  map_add := coe_add _ _
  map_mul := coe_mul _ _

instance : IsAlgebra R (R√d) where
  commutes _ _ := mul_comm _ _
  smul_def := smul_eq_coe_mul

end Rsqrtd
