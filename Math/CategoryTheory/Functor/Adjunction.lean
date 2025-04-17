import Math.CategoryTheory.Impls.Func

namespace Category.Functor

variable [Category C] [Category D]

class Adjunction (F: C ⥤ D) (G: D ⥤ C) where
  unit : 𝟭 C ⟶ (G ⋙ F)
  counit: (F ⋙ G) ⟶ 𝟭 D
  counit_unit (X: C): counit.app (F.obj X) ≫ F.map (unit.app X) = 𝟙 _
  unit_counit (Y: D): G.map (counit.app Y) ≫ unit.app (G.obj Y) = 𝟙 _

end Category.Functor
