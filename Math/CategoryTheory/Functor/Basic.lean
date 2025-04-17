import Math.CategoryTheory.Basic

namespace Category

@[ext]
structure Functor (C D: Type*) [Category C] [Category D] where
  obj: C -> D
  map: ∀{X Y: C}, X ⟶ Y -> obj X ⟶ obj Y
  map_id: ∀{X: C}, map (𝟙 X) = 𝟙 (obj X) := by intros; simp; try rfl
  map_comp: ∀{X Y Z: C} (f: Y ⟶ Z) (g: X ⟶ Y), map (f ≫ g) = map f ≫ map g := by intros; try simp; try rfl

scoped infixr:26 " ⥤ " => Functor

attribute [simp] Functor.map_id Functor.map_comp

protected def Functor.id (C: Type*) [Category C] : C ⥤ C where
  obj X := X
  map f := f

scoped notation "𝟭" => Functor.id

namespace Functor

section

variable {C D: Type*} [Category C] [Category D]

instance : Inhabited (C ⥤ C) :=
  ⟨𝟭 C⟩

@[simp]
def id_obj (X : C) : (𝟭 C).obj X = X := rfl

@[simp]
def id_map {X Y : C} (f : X ⟶ Y) : (𝟭 C).map f = f := rfl

protected class IsFaithful (f: C ⥤ D) : Prop where
  protected map_inj: ∀{X Y: C}, Function.Injective (@f.map X Y)
protected class IsFull (f: C ⥤ D) : Prop where
  protected map_surj: ∀{X Y: C}, Function.Surjective (@f.map X Y)
protected class IsFullyFaithful (f: C ⥤ D) : Prop extends f.IsFaithful, f.IsFull where

def map_inj (f: C ⥤ D) [h: f.IsFaithful] : ∀{X Y: C}, Function.Injective (@f.map X Y) := @h.map_inj
def map_surj (f: C ⥤ D) [h: f.IsFull] : ∀{X Y: C}, Function.Surjective (@f.map X Y) := h.map_surj

end

variable {C D E: Type*} [Category C] [Category D] [Category E]

def comp (F: D ⥤ E) (G: C ⥤ D) : C ⥤ E where
  obj X := F.obj (G.obj X)
  map f := F.map (G.map f)

@[simp]
def comp_obj (F: D ⥤ E) (G: C ⥤ D) (X: C) :
    (F.comp G).obj X = F.obj (G.obj X) := rfl

@[simp]
def comp_map (F: D ⥤ E) (G: C ⥤ D) {X Y : C} (f: X ⟶ Y) :
    (F.comp G).map f = F.map (G.map f) := rfl

end Functor

/-- Notation for composition of functors. -/
scoped infixr:80 " ⋙ " => Functor.comp

namespace Functor

variable {C D E F: Type*} [Category C] [Category D] [Category E] [Category F]

@[simp] def comp_id (f: C ⥤ D) : f ⋙ 𝟭 _ = f := rfl
@[simp] def id_comp (f: C ⥤ D) : 𝟭  _⋙ f = f := rfl
@[simp] def comp_assoc (f: E ⥤ F) (g: D ⥤ E) (h: C ⥤ D) :
  f ⋙ g ⋙ h = (f ⋙ g) ⋙ h := rfl

end Functor

class Concrete.{u} (C: Type*) [Category C] where
  toSet : C ⥤ Type u
  toSet_faithful: toSet.IsFaithful := by infer_instance

def toSet (C: Type*) [Category C] [h: Concrete C] : C ⥤ Type _ := h.toSet
def toSet_faithful (C: Type*) [Category C] [h: Concrete C] : (toSet C).IsFaithful := h.toSet_faithful

-- def IsFree [Category C] [Concrete C] (c: C) :  := sorry

end Category
