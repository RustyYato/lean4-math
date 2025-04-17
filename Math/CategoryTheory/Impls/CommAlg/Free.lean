import Math.CategoryTheory.Impls.CommAlg.Defs
import Math.CategoryTheory.Functor.Adjunction
import Math.Data.MvPoly.Eval

noncomputable section

namespace Category

variable (R: Type v) [SemiringOps R] [IsSemiring R] [IsCommMagma R]

open Classical



def CommAlg.Free : Type u ⥤ CommAlg.{max u v, v} R where
  obj α := CommAlg.mk (Alg.mk (MvPoly R α))
  map {X Y} := MvPoly.map
  map_id {X} := AlgHom.ext _ _ (fun x => MvPoly.lift_X x)
  map_comp {X Y Z} f g := (MvPoly.map_comp_map _ _).symm


section


variable
  [SemiringOps R] [SemiringOps A] [SemiringOps B] [SemiringOps C]
  [AlgebraMap R A] [AlgebraMap R B] [AlgebraMap R C]

def AlgHom.comp_congr (f₀ f₁: B →ₐ[R] C) (g₀ g₁: A →ₐ[R] B) :
  f₀ = f₁ -> g₀ = g₁ -> f₀.comp g₀ = f₁.comp g₁ := by
  rintro rfl rfl; rfl

end

namespace CommAlg.Free

variable {A: CommAlg R} {B: CommAlg R}

def inj : σ -> (CommAlg.Free R).obj σ := MvPoly.X

@[irreducible]
-- show that MvPoly is the free commutative P-algebra over σ
def lift : (σ -> A) ≃ ((CommAlg.Free R).obj σ ⟶ A) := MvPoly.lift

def map (f: σ -> σ') : (CommAlg.Free R).obj σ ⟶ (CommAlg.Free R).obj σ' :=
  lift R (inj R ∘ f)

@[simp]
def free_map_eq_map (f: σ -> σ') : (CommAlg.Free R).map f = map R f := by
  simp [Category.Functor.map, CommAlg.Free, map, MvPoly.map, inj, lift]
  rfl

def inj_natural : ∀f: α -> β, CommAlg.Free.inj R ≫ (𝟭 (Type _)).map f = (toSet (CommAlg R) ⋙ CommAlg.Free R).map f ≫ CommAlg.Free.inj R := by
  intro f; apply funext; intro x; symm; apply MvPoly.apply_map_X

def lift_natural : ∀ (f : A →ₐ[R] B), lift R id ≫ (CommAlg.Free R ⋙ toSet (CommAlg R)).map f = (𝟭 (CommAlg R)).map f ≫ lift R id := by
  intro f
  apply AlgHom.ext
  show ∀_: MvPoly R A, _
  intro x
  simp only [Category.comp, Functor.comp, toSet, Concrete.toSet, CommAlg.toSet,
    CommAlg.Free, Functor.id]
  unfold lift
  erw [MvPoly.lift_comp_map_algmap]
  rfl

def lift_inj : (toSet (CommAlg R)).map (lift R id) ≫ inj R = 𝟙 ((toSet (CommAlg R)).obj Y) := by
  simp [toSet, Concrete.toSet, CommAlg.toSet]
  apply funext
  intro y
  rw [lift, inj]
  apply MvPoly.apply_lift_X

def lift_id_comp_map_X : (lift R id) ≫ (map R (inj R)) = 𝟙 ((CommAlg.Free R).obj σ) := by
  show _ = AlgHom.id (MvPoly R σ)
  simp [lift, map, inj, MvPoly.map, Category.comp]
  apply MvPoly.lift_id_comp_map_X

def inj_lift :  (CommAlg.Free.lift R) id ≫ (CommAlg.Free R).map (CommAlg.Free.inj R) =
  𝟙 ((CommAlg.Free R).obj ((𝟭 (Type _)).obj X)) := by
  simp; apply lift_id_comp_map_X R

end CommAlg.Free

instance : Functor.Adjunction (CommAlg.Free R) (toSet (CommAlg R)) where
  unit := {
    app _ := CommAlg.Free.inj R
    naturality {_ _} := CommAlg.Free.inj_natural R
  }
  counit := {
    app _ := CommAlg.Free.lift R id
    naturality {_ _} := CommAlg.Free.lift_natural R
  }
  unit_counit _ := CommAlg.Free.lift_inj R
  counit_unit _ := CommAlg.Free.inj_lift R

end Category

end
