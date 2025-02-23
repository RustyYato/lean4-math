import Math.CategoryTheory.Basic
import Math.CategoryTheory.Functor.Basic

namespace Category

@[pp_with_univ]
structure Cat.{v, u} where
  Ty: Type u
  [cat: Category.{v, u} C]

attribute [coe] Cat.Ty
instance (C: Cat) : Category C.Ty := C.cat
instance : CoeSort Cat.{v, u} (Type u) := ⟨Cat.Ty⟩

instance : LargeCategory Cat where
  Hom A B := A ⥤ B
  id A := 𝟭 A
  comp F G := F ⋙ G

end Category
