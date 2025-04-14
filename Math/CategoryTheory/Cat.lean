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

-- the forgetful functor from Cat to Set
def Cat.toSet : Cat.{v, u} ⥤ Type u where
  obj := Cat.Ty
  map := Functor.obj
  map_id := by intros; rfl
  map_comp := by intros; rfl

end Category
