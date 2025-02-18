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
      rw [resp_add, add_smul]
      rfl
    zero_smul x := by
      show f 0 • x = 0
      rw [resp_zero, zero_smul]
  }
