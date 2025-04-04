import Math.Algebra.Ring.Defs
import Math.Algebra.Module.LinearMap.Defs
import Math.Data.FinSupp.Algebra

def FreeModule (R M: Type*) [SemiringOps R] [IsSemiring R] [DecidableEq M]
  := Finsupp M R (Finset M)

namespace FreeModule

section

variable {R M: Type*} [SemiringOps R] [IsSemiring R] [DecidableEq M]

instance : AddMonoidOps (FreeModule R M) := inferInstanceAs (AddMonoidOps (Finsupp M R (Finset M)))
instance : SMul R (FreeModule R M) := inferInstanceAs (SMul R (Finsupp M R (Finset M)))

instance : IsAddMonoid (FreeModule R M) := inferInstanceAs (IsAddMonoid (Finsupp M R (Finset M)))
instance : IsAddCommMagma (FreeModule R M) := inferInstanceAs (IsAddCommMagma (Finsupp M R (Finset M)))
instance : IsModule R (FreeModule R M) := inferInstanceAs (IsModule R (Finsupp M R (Finset M)))

end

section

variable {R M: Type*} [RingOps R] [IsRing R] [DecidableEq M]

instance : AddGroupOps (FreeModule R M) := inferInstanceAs (AddGroupOps (Finsupp M R (Finset M)))
instance : IsAddGroup (FreeModule R M) := inferInstanceAs (IsAddGroup (Finsupp M R (Finset M)))

end

variable {R M: Type*} [SemiringOps R] [IsSemiring R] [DecidableEq M]

def ofFinsupp (f: Finsupp M R (Finset M)) : FreeModule R M := f
def toFinsupp (f: FreeModule R M) : Finsupp M R (Finset M) := f

def equivFinsupp : FreeModule R M ≃ₗ[R] Finsupp M R (Finset M) :=
  LinearEquiv.refl _ _

instance : FunLike (FreeModule R M) M R :=
  inferInstanceAs (FunLike (Finsupp M R (Finset M)) M R)

variable {N: Type*} [AddMonoidOps N] [IsAddMonoid N] [IsAddCommMagma N] [SMul R N] [IsModule R N]

private def toFreeModuleHom (f: M -> N) (a: FreeModule R M) : N :=
 (equivFinsupp a).sum (fun m r => r • f m) <| by
    intro m hm
    simp [hm]

private def preLift (f: M -> N) : FreeModule R M →ₗ[R] N where
  toFun := toFreeModuleHom f
  map_add {x y} := by
    simp [toFreeModuleHom, map_add]
    rw [Finsupp.add_sum]
    intro m a b
    rw [add_smul]
  map_smul {r₀ x} := by
    simp [toFreeModuleHom, map_smul]
    rw [Finsupp.smul_sum]
    intro i a
    rw [mul_smul]

def lift : (M -> N) ≃ (FreeModule R M →ₗ[R] N) where
  toFun := preLift
  invFun f m := f (equivFinsupp.symm (Finsupp.single m 1))
  leftInv := by
    intro f
    simp; ext m
    show toFreeModuleHom f (equivFinsupp.symm (Finsupp.single m 1)) = f m
    unfold FreeModule.toFreeModuleHom
    erw [Equiv.symm_coe, Finsupp.single_sum, one_smul]
  rightInv := by
    classical
    intro f; ext a
    simp
    show toFreeModuleHom _ _ = f a
    unfold FreeModule.toFreeModuleHom
    simp
    conv => {
      lhs; arg 2; intro m r
      rw [←map_smul, ←map_smul, Finsupp.smul_single, mul_one]
    }
    show a.sum (fun m r => f (Finsupp.single m r)) _ = f a
    rw [←Finsupp.map_sum, Finsupp.sum_single]

end FreeModule
