import Math.Algebra.Monoid.Action.Hom
import Math.Algebra.Module.Defs

def IsModule.compHom
  [SemiringOps R] [SemiringOps S] [AddMonoidOps M]
  [IsSemiring R] [IsSemiring S] [IsAddMonoid M] [IsAddCommMagma M]
  [SMul R M] [IsModule R M]
  (f: S →+* R): @IsModule S M (SMul.comp f) _ _ _ _ _ :=
  let _smul: SMul S M := (SMul.comp f)
  {
    IsDistribMulAction.compHom f.toGroupHom with
    add_smul r s x := by
      show (f (r + s)) • x = _
      rw [map_add, add_smul]
      rfl
    zero_smul x := by
      show f 0 • x = 0
      rw [map_zero, zero_smul]
  }

variable [SemiringOps α] [SemiringOps β] [IsSemiring α] [IsSemiring β]

def RingHom.toSMul (f: α →+* β) : SMul α β where
  smul a b := f a * b

def RingHom.toIsModule (f: α →+* β) :
  have := f.toSMul
  IsModule α β :=
  let _ := f.toSMul
  {
    one_smul m := by
      show f 1 * m = m
      rw [map_one, one_mul]
    mul_smul x y m := by
      show f (x * y) * m = f (x) * (f (y) * m)
      rw [map_mul, mul_assoc]
    smul_zero _ := mul_zero _
    smul_add _ _ _ := mul_add _ _ _
    add_smul r s m := by
      show f (r + s) * m = _
      rw [map_add, add_mul]; rfl
    zero_smul m := by
      show f 0 * m = 0
      rw [map_zero, zero_mul]
  }
