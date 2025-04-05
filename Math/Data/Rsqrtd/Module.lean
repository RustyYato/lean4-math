import Math.Data.Rsqrtd.Basic
import Math.Algebra.Module.Defs

namespace Rsqrtd

variable {R: Type*} [SemiringOps R] [IsSemiring R] [IsCommMagma R] {d: R}

instance : IsModule R (R√d) where
  one_smul a := by simp [smul_eq_coe_mul]
  mul_smul a b c := by
    simp [smul_eq_coe_mul]
    apply mul_assoc
  zero_smul := by simp [smul_eq_coe_mul]
  smul_zero := by simp [smul_eq_coe_mul]
  smul_add a x y := by simp [smul_eq_coe_mul]; rw [mul_add]
  add_smul a x y := by simp [smul_eq_coe_mul]; rw [add_mul]

end Rsqrtd
