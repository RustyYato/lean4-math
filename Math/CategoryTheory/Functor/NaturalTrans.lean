import Math.CategoryTheory.Functor.Basic

namespace Category.Functor

variable [Category C] [Category D]

structure NaturalTrans (F G: C ⥤ D) where
  app : ∀ X : C, F.obj X ⟶ G.obj X
  naturality : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), app Y ≫ F.map f = G.map f ≫ app X := by intros; simp

namespace NaturalTrans

variable {F G H I: C ⥤ D}

def id (F: C ⥤ D) : NaturalTrans F F where
  app _ := 𝟙 _

def comp (f: NaturalTrans G H) (g: NaturalTrans F G) : NaturalTrans F H where
  app _ := f.app _ ≫ g.app _
  naturality := by
    intro x y f'
    rw [←Category.comp_assoc]
    simp [f.naturality, g.naturality]

@[simp]
def id_comp (f: NaturalTrans F G) : comp (id G) f = f := by
  simp [id, comp]

@[simp]
def comp_id (f: NaturalTrans F G) : comp f (id F) = f := by
  simp [id, comp]

@[simp]
def comp_assoc
  (h: NaturalTrans H I)
  (g: NaturalTrans G H)
  (f: NaturalTrans F G) : comp h (comp g f) = comp (comp h g) f := by
  simp [id, comp]

end NaturalTrans

end Category.Functor
