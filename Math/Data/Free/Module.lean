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

def single (m: M) (r: R) : FreeModule R M := Finsupp.single m r

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

private def apply_lift (f: M -> N) : lift (R := R) f x = toFreeModuleHom f x := by
  rfl

def apply_lift_single (r: R) (f: M -> N) : lift f (single m r) = r • f m := by
  rw [apply_lift]
  apply Finsupp.single_sum

def apply_lift_single' (x: FreeModule R M) : lift (fun x => single x 1) x = x := by
  rw [apply_lift]
  unfold toFreeModuleHom
  classical
  simp [single, Finsupp.smul_single]
  rw [Finsupp.sum_single]

def lift_lift [DecidableEq α] (f: M -> α) (g: α -> N) :
  (lift (R := R) g).comp (lift (fun x => single (f x) (1: R))) = (lift (R := R) (fun x => g (f x))) := by
  ext m
  rw [LinearMap.apply_comp]
  induction m using Finsupp.induction with
  | zero => rfl
  | single =>
    repeat erw [apply_lift_single]
    classical
    erw [Finsupp.smul_single]
    simp [apply_lift_single']
    rw [apply_lift]
    unfold toFreeModuleHom
    rw [Finsupp.single_sum]
  | add a b iha ihb h =>
    rw [map_add,map_add, map_add, iha, ihb]

def lin_equiv_of_equiv [DecidableEq α] [DecidableEq β] (h: α ≃ β) : FreeModule R α ≃ₗ[R] FreeModule R β := {
  lift (fun x => single (h x) 1) with
  toFun := lift (fun x => single (h x) 1)
  invFun := lift (fun x => single (h.symm x) 1)
  leftInv x := by
    rw [←LinearMap.apply_comp, lift_lift]
    simp [apply_lift_single']
  rightInv x := by
    rw [←LinearMap.apply_comp, lift_lift]
    simp [apply_lift_single']
}

end FreeModule
