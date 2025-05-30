import Math.Algebra.Module.LinearMap.Defs
import Math.Data.Finsupp.Algebra

def FreeModule (R M: Type*) [Zero R] := Finsupp M R (LazyFinset M)

namespace FreeModule

variable {R M: Type*} [SemiringOps R] [IsSemiring R]

instance : AddMonoidOps (FreeModule R M) := inferInstanceAs (AddMonoidOps (Finsupp _ _ _))
instance : IsAddMonoid (FreeModule R M) := inferInstanceAs (IsAddMonoid (Finsupp _ _ _))
instance : IsAddCommMagma (FreeModule R M) := inferInstanceAs (IsAddCommMagma (Finsupp _ _ _))
instance : SMul R (FreeModule R M) := inferInstanceAs (SMul R (Finsupp _ _ _))
instance : IsModule R (FreeModule R M) := inferInstanceAs (IsModule R (Finsupp _ _ _))

end FreeModule

namespace FreeModule

variable {R M: Type*} [RingOps R] [IsRing R]

instance : AddGroupOps (FreeModule R M) := inferInstanceAs (AddGroupOps (Finsupp _ _ _))
instance : IsAddGroup (FreeModule R M) := inferInstanceAs (IsAddGroup (Finsupp _ _ _))

end FreeModule

namespace FreeModule

variable {R M: Type*} [SemiringOps R] [IsSemiring R] [DecidableEq M]

instance : FunLike (FreeModule R M) M R :=
  inferInstanceAs (FunLike (Finsupp M R (LazyFinset M)) M R)

variable {α N: Type*} [AddMonoidOps N] [IsAddMonoid N] [IsAddCommMagma N] [SMul R N] [IsModule R N]
   [AddMonoidOps α] [IsAddMonoid α] [IsAddCommMagma α] [SMul R α] [IsModule R α]

private def toFreeModuleHom (f: M -> N) (a: FreeModule R M) : N :=
 a.sum (fun m r => r • f m) <| by
    intro m hm
    simp [hm]

def single (m: M) (r: R) : FreeModule R M := Finsupp.single m r

def ι (R: Type*) [Zero R] [One R] (m: M) : FreeModule R M := Finsupp.single m 1

def apply_ι (m v: M) : ι R m v = if v = m then 1 else 0 := Finsupp.apply_single _

def ι_inj [IsNontrivial R] : Function.Injective (ι R (M := M)) := by
  intro x y h
  have : ι R y x = ι R x x := by rw [h]
  rw [apply_ι, apply_ι, if_pos rfl] at this
  split at this
  assumption
  exact (zero_ne_one R this).elim

instance [Subsingleton R] : Subsingleton (FreeModule R M) where
  allEq a b := by
    apply Finsupp.ext
    intro m
    apply Subsingleton.allEq

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
  invFun f m := f (ι R m)
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
    unfold ι
    conv => {
      lhs; arg 2; intro m r
      rw [←map_smul, Finsupp.smul_single, mul_one]
    }
    show a.sum (fun m r => f (Finsupp.single m r)) _ = f a
    rw [←Finsupp.map_sum, Finsupp.sum_single]

private def apply_lift (f: M -> N) : lift (R := R) f x = toFreeModuleHom f x := by
  rfl

def apply_lift_ι (f: M -> N) : lift f (ι R m) = f m := by
  rw [apply_lift]
  unfold toFreeModuleHom
  rw [ι, Finsupp.single_sum, one_smul]

@[induction_eliminator]
def induction {motive: FreeModule R M -> Prop}
  (zero: motive 0)
  (ι: ∀m, motive (ι R m))
  (smul: ∀(r: R) (a: FreeModule R M), r ≠ 0 -> motive a -> motive (r • a))
  (add: ∀(a b: FreeModule R M), motive a -> motive b ->
    (∀x, a x + b x = 0 -> a x = 0 ∧ b x = 0) ->
    Set.support a ∩ Set.support b = ∅ ->
    motive (a + b)):
  ∀a, motive a := by
  classical
  intro a
  induction a using Finsupp.induction with
  | zero => apply zero
  | add => apply add <;> assumption
  | single m r =>
    by_cases hr:r = 0
    subst r
    rw [show Finsupp.single m (0: R) = 0 from ?_]
    apply zero
    ext v; rw [Finsupp.apply_single]
    split <;> rfl
    rw [←mul_one r, ←Finsupp.smul_single]
    apply smul
    assumption
    apply ι

def lift_ι : lift (M := M) (ι R) x = x := by
  induction x with
  | zero => rfl
  | ι => rw [apply_lift_ι]
  | smul _ _ _ ih => rw [map_smul, ih]
  | add _ _ iha ihb => rw [map_add, iha, ihb]

def map_comp_lift (f: M -> α) (g: α →ₗ[R] N) :
  g.comp (lift (R := R) f) = lift (g ∘ f) := by
  ext x
  induction x with
  | zero => rw [map_zero, map_zero]
  | ι =>
    rw [LinearMap.apply_comp, apply_lift_ι, apply_lift_ι, ]
    rfl
  | smul r x hr ih => rw [map_smul, map_smul, ih]
  | add a b iha ihb => rw [map_add, map_add, iha, ihb]

def lin_equiv_of_equiv [DecidableEq α] [DecidableEq β] (h: α ≃ β) : FreeModule R α ≃ₗ[R] FreeModule R β := {
  lift (fun x => single (h x) 1) with
  toFun := lift (fun x => ι R (h x))
  invFun := lift (fun x => ι R (h.symm x))
  leftInv x := by
    rw [←LinearMap.apply_comp]
    simp [map_comp_lift, apply_lift_ι, lift_ι, Function.comp_def]
  rightInv x := by
    rw [←LinearMap.apply_comp]
    simp [map_comp_lift, apply_lift_ι, lift_ι, Function.comp_def]
}

instance [Subsingleton R] : Subsingleton (FreeModule R M) where
  allEq a b := by
    apply Finsupp.ext
    intro; apply Subsingleton.allEq

attribute [irreducible] lift

end FreeModule
