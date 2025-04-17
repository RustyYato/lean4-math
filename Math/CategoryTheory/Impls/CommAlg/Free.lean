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

-- prove that MvPoly is the left adjoint to the forgetful functor to Set
instance : Functor.Adjunction (CommAlg.Free R) (toSet (CommAlg R)) where
  unit := {
    app X := MvPoly.X
    naturality {X Y} f := by
      apply funext; intro x; symm; apply MvPoly.apply_map_X
  }
  counit := {
    app X := MvPoly.lift (P := R) id
    naturality {X Y} := by
      show ∀f: X →ₐ[R] Y, _
      intro f
      apply AlgHom.ext
      show ∀_: MvPoly R X, _
      intro x
      show MvPoly.lift id (MvPoly.map f x) = f ((MvPoly.lift id) x)
      rw [←AlgHom.apply_comp]
      rw [MvPoly.lift_comp_map_algmap]
      rfl
  }
  unit_counit Y := by
    simp only [Functor.id, toSet, Concrete.toSet, CommAlg.toSet, comp, CommAlg.Free,
      Function.comp_def, Category.id]
    apply funext; intro x
    erw [MvPoly.apply_lift_X]
  counit_unit X := by
    simp only [CommAlg.Free, inferInstance, Functor.id, comp, CommAlg.toType, toSet, Concrete.toSet,
      CommAlg.toSet, instSemiringOpsToType, instAlgebraMapToType, Functor.comp, Category.id]
    -- stupid lean putting a classical in here
    erw [Subsingleton.allEq (fun a b: MvPoly R X => Classical.propDecidable _)]
    apply MvPoly.lift_id_comp_map_X

end Category

end
