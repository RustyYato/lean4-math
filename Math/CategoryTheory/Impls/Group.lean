import Math.CategoryTheory.Basic
import Math.Algebra.Group.Defs
import Math.Algebra.Group.Hom

namespace Category

structure Grp where
  Elem: Type u
  [ops: GroupOps G]
  [inst: IsGroup G]

attribute [coe] Grp.Elem

instance : CoeSort Grp (Type u) where
  coe := Grp.Elem

instance (G: Grp) : GroupOps G := G.ops
instance (G: Grp) : IsGroup G := G.inst

instance : Category Grp where
  Hom a b := a →* b
  id _ := GroupHom.id _
  comp := GroupHom.comp

end Category
