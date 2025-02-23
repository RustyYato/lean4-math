import Math.Type.Notation
import Math.Tactics.PPWithUniv
import Math.Data.Opposite

@[pp_with_univ]
class Category.{v, u} (α: Type u) where
  Hom : α -> α -> Type v
  id : ∀a, Hom a a
  comp : ∀{a b c: α}, Hom b c -> Hom a b -> Hom a c
  id_comp: ∀{a b} (h: Hom a b), comp (id b) h = h := by intros; simp; try rfl
  comp_id: ∀{a b} (h: Hom a b), comp h (id a) = h := by intros; simp; try rfl
  comp_assoc: ∀{a b c d: α} (f: Hom c d) (g: Hom b c) (h: Hom a b),
    comp f (comp g h) = comp (comp f g) h := by intros; simp; try rfl

namespace Category

scoped infixr:30 " ⟶ " => Category.Hom
scoped notation "𝟙" => Category.id
scoped infixr:80 " ≫ " => Category.comp

attribute [simp] Category.id_comp Category.comp_id Category.comp_assoc

abbrev LargeCategory (C : Type (u + 1)) : Type (u + 1) := Category.{u} C

/-- A `SmallCategory` has objects and morphisms in the same universe level.
-/
abbrev SmallCategory (C : Type u) : Type (u + 1) := Category.{u} C

-- the category with all the arrows swapped
def Opp (C: Category.{v, u} α) : Category.{v, u} αᵒᵖ where
  Hom a b := b.get ⟶ a.get
  id x := 𝟙 x.get
  comp h g := g ≫ h
  id_comp := C.comp_id
  comp_id := C.id_comp
  comp_assoc _ _ _ := (C.comp_assoc _ _ _).symm

scoped postfix:max "ᵒᵖ" => Opp

instance (α: Type u) [C: Category.{v, u} α] : Category.{v, u} αᵒᵖ := Cᵒᵖ

def hom_to_opp {a b: C} [Category C] (f: a ⟶ b) : Opposite.mk b ⟶ Opposite.mk a := f

section

variable [Category C] {X Y Z: C}

class Epi (f: X ⟶ Y) where
  right_cancel: ∀{Z: C} (g h: Y ⟶ Z), g ≫ f = h ≫ f -> g = h

class Mono (f: X ⟶ Y) where
  left_cancel: ∀{Z: C} (g h: Z ⟶ X), f ≫ g = f ≫ h -> g = h

instance : Epi (𝟙 X) where
  right_cancel _ _ h := by
    simp at h; assumption

instance : Mono (𝟙 X) where
  left_cancel _ _ h := by
    simp at h; assumption

def cancel_epi (f: X ⟶ Y) [Epi f] {g h: Y ⟶ Z} : g ≫ f = h ≫ f ↔ g = h := by
  apply Iff.intro
  apply Epi.right_cancel
  rintro rfl; rfl

def cancel_mono (f: X ⟶ Y) [Mono f] {g h: Z ⟶ X} : f ≫ g = f ≫ h ↔ g = h := by
  apply Iff.intro
  apply Mono.left_cancel
  rintro rfl; rfl

def cancel_epi_id (f: X ⟶ Y) [Epi f] {g: Y ⟶ Y} : g ≫ f = f ↔ g = 𝟙 Y := by
  conv => { lhs; rhs; rw [←id_comp f] }
  apply cancel_epi

def cancel_mono_id (f: X ⟶ Y) [Mono f] {g: X ⟶ X} : f ≫ g = f ↔ g = 𝟙 X := by
  conv => { lhs; rhs; rw [←comp_id f] }
  apply cancel_mono

instance {a b: C} (f: a ⟶ b) [Mono f] : Epi (hom_to_opp f) where
  right_cancel _ _ := (cancel_mono f).mp

instance {a b: C} (f: a ⟶ b) [Epi f] : Mono (hom_to_opp f) where
  left_cancel _ _ := (cancel_epi f).mp

instance {f: Y ⟶ Z} {g: X ⟶ Y} [Epi f] [Epi g] : Epi (f ≫ g) where
  right_cancel {Z} h₀ h₁ eq := by
    rw [comp_assoc, comp_assoc] at eq
    exact Epi.right_cancel _ _ (Epi.right_cancel _ _ eq)

instance {f: Y ⟶ Z} {g: X ⟶ Y} [Mono f] [Mono g] : Mono (f ≫ g) where
  left_cancel {Z} h₀ h₁ eq := by
    rw [←comp_assoc, ←comp_assoc] at eq
    exact Mono.left_cancel _ _ (Mono.left_cancel _ _ eq)

def epi_of_comp {f: Y ⟶ Z} {g: X ⟶ Y} [Epi (f ≫ g)] : Epi f where
  right_cancel := by
    intro Z h₀ h₁ eq
    have : (h₀ ≫ f) ≫ g = (h₁ ≫ f) ≫ g := by rw [eq]
    rw [←comp_assoc, ←comp_assoc] at this
    exact (cancel_epi _).mp this

def mono_of_comp {f: Y ⟶ Z} {g: X ⟶ Y} [Mono (f ≫ g)] : Mono g where
  left_cancel := by
    intro Z h₀ h₁ eq
    have : f ≫ (g ≫ h₀) = f ≫ (g ≫ h₁) := by rw [eq]
    rw [comp_assoc, comp_assoc] at this
    exact (cancel_mono _).mp this

end

-- The category of all small "sets" (since we are in a type theory, we use `Type u`)
-- instead of `Set`
@[pp_with_univ]
instance Set.{u} : LargeCategory (Type u) where
  Hom α β := α -> β
  id _ := _root_.id
  comp f g := f ∘ g

end Category
