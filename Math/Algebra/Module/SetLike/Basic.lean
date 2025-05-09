import Math.Algebra.Module.SetLike.Defs
import Math.Algebra.Semiring.SetLike.Basic
import Math.Algebra.Module.Defs

variable
  [SemiringOps R] [IsSemiring R]
  [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M]
  [SMul R M] [IsModule R M]
  [SetLike S M] [IsSubmodule S R]
  (s: Submodule R M)

instance : SMul R s where
  smul r x := ⟨r • x.val, mem_smul _ _ x.property⟩

@[simp]
def smul_val (r: R) (x: s) : (r • x).val = r • x.val := rfl

instance : IsModule R s where
  one_smul _ := by
    apply Subtype.val_inj
    apply one_smul
  mul_smul _ _ _ := by
    apply Subtype.val_inj
    apply mul_smul
  smul_zero _ := by
    apply Subtype.val_inj
    apply smul_zero
  smul_add _ _ _ := by
    apply Subtype.val_inj
    apply smul_add
  zero_smul _ := by
    apply Subtype.val_inj
    apply zero_smul
  add_smul _ _ _ := by
    apply Subtype.val_inj
    apply add_smul

variable [FunLike F M N]

variable [SemiringOps N] [IsSemiring N] [SMul R N]
  [IsZeroHom F M N] [IsAddHom F M N] [IsSMulHom F R M N]

namespace Submodule

def preimage (f: F) (s: Submodule R N) : Submodule R M := {
  s.toAddSubmonoid.preimage f, s.toSubMulAction.preimage f with
}

def image (f: F) (s: Submodule R M) : Submodule R N := {
  s.toAddSubmonoid.image f, s.toSubMulAction.image f with
}

def range (f: F) : Submodule R N := {
  AddSubmonoid.range f, SubMulAction.range f with
}

end Submodule
