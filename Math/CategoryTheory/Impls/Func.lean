import Math.CategoryTheory.Functor.NaturalTrans


namespace Category.Functor

variable [Category C] [Category D]

instance : Category (C ⥤ D) where
  Hom := NaturalTrans
  id := NaturalTrans.id
  comp := NaturalTrans.comp
  id_comp := by intros; simp
  comp_id := by intros; simp
  comp_assoc := by intros; simp

end Category.Functor
