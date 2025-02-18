import Math.Algebra.Hom.Defs
import Math.Algebra.Monoid.Action.Defs

def SMul.comp [SMul R A] (f: S -> R) : SMul S A where
  smul s a := f s • a

def IsMulAction.compHom
  [MonoidOps R] [MonoidOps S]
  [IsMonoid R] [IsMonoid S]
  [SMul R M] [IsMulAction R M]
  (f: S →* R): @IsMulAction S M (SMul.comp f) _ _ :=
  let _smul: SMul S M := (SMul.comp f)
  {
    one_smul a := by
      show (f 1) • a = a
      rw [resp_one, one_smul]
    mul_smul := by
      intro x y b
      show (f _) • _ = _
      rw [resp_mul, mul_smul]
      rfl
  }

def IsDistribMulAction.compHom
  [MonoidOps R] [MonoidOps S] [AddMonoidOps M]
  [IsMonoid R] [IsMonoid S] [IsAddMonoid M]
  [SMul R M] [IsDistribMulAction R M]
  (f: S →* R): @IsDistribMulAction S M (SMul.comp f) _ _ _ _ :=
  let _smul: SMul S M := (SMul.comp f)
  {
    IsMulAction.compHom f with
    smul_zero a := smul_zero (f a)
    smul_add a := smul_add (f a)
  }
