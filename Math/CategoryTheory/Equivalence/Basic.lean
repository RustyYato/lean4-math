import Math.CategoryTheory.Functor.Basic

namespace Category

@[ext]
structure Equivalence (C D: Type*) [Category C] [Category D] where
  toFun: C ⥤ D
  invFun: D ⥤ C


end Category
