import Math.Algebra.Module.LinearMap.Defs
import Math.Data.FinSupp.Algebra

abbrev FreeModule (R M: Type*) [Zero R] [DecidableEq M]
  := Finsupp M R (Finset M)

namespace FreeModule

variable {R M: Type*} [SemiringOps R] [IsSemiring R] [DecidableEq M]

instance : FunLike (FreeModule R M) M R :=
  inferInstanceAs (FunLike (Finsupp M R (Finset M)) M R)

variable {N: Type*} [AddMonoidOps N] [IsAddMonoid N] [IsAddCommMagma N] [SMul R N] [IsModule R N]

private def toFreeModuleHom (f: M -> N) (a: FreeModule R M) : N :=
 a.sum (fun m r => r • f m) <| by
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
  invFun f m := f (Finsupp.single m 1)
  leftInv := by
    intro f
    simp; ext m
    show toFreeModuleHom f (Finsupp.single m 1) = f m
    unfold FreeModule.toFreeModuleHom
    erw [Finsupp.single_sum, one_smul]
  rightInv := by
    classical
    intro f; ext a
    simp
    show toFreeModuleHom _ _ = f a
    unfold FreeModule.toFreeModuleHom
    simp
    conv => {
      lhs; arg 2; intro m r
      rw [←map_smul, Finsupp.smul_single, mul_one]
    }
    show a.sum (fun m r => f (Finsupp.single m r)) _ = f a
    rw [←Finsupp.map_sum, Finsupp.sum_single]

end FreeModule
