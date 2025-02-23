import Math.CategoryTheory.Basic

namespace Category

structure Isomorphism {C: Type*} [Category C] (X Y: C) where
  hom: X ⟶ Y
  inv: Y ⟶ X
  leftInv : hom ≫ inv = 𝟙 _ := by simp; try rfl
  rightInv : inv ≫ hom = 𝟙 _ := by simp; try rfl

attribute [simp] Isomorphism.leftInv Isomorphism.rightInv

infixr:10 " ≅ " => Isomorphism -- type as \cong or \iso

namespace Isomorphism

variable {C: Type*} [Category C] {X Y Z: C}

@[ext]
def ext (h g: X ≅ Y) (eq: h.hom = g.hom) : h = g := by
  cases h with | mk toFun invFun₀ =>
  cases g with | mk toFun invFun₁ =>
  congr
  dsimp at eq
  cases eq
  rename_i _ g h _
  rw [←comp_id invFun₀, ←h, comp_assoc, g, id_comp]

def refl (X: C) : X ≅ X where
  hom := 𝟙 _
  inv := 𝟙 _

instance : Inhabited (X ≅ X) := ⟨refl X⟩

def symm (h: X ≅ Y) : Y ≅ X where
  hom := h.inv
  inv := h.hom

@[simp] def symm_hom (h : X ≅ Y) : h.symm.hom = h.inv := rfl
@[simp] def symm_inv (h : X ≅ Y) : h.symm.inv = h.hom := rfl
@[simp] def symm_symm (h : X ≅ Y) : h.symm.symm = h := rfl

def trans (h: X ≅ Y) (g: Y ≅ Z) : X ≅ Z where
  hom := g.hom ≫ h.hom
  inv := h.inv ≫ g.inv
  leftInv := by
    rw [←comp_assoc]
    simp
  rightInv := by
    rw [←comp_assoc]
    simp

end Isomorphism

end Category
