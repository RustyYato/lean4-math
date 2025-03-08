import Math.CategoryTheory.Basic
import Math.Algebra.Group.Theory.Basic

namespace Category

variable [Category α] {x: α}

structure Aut (x: α) where
  toFun: x ⟶ x
  invFun: x ⟶ x
  leftInv: invFun ≫ toFun = 𝟙 x
  rightInv: toFun ≫ invFun = 𝟙 x

@[ext]
def Aut.ext (a b: Aut x) : a.toFun = b.toFun -> a = b := by
  intro h
  suffices a.invFun = b.invFun by
    cases a; cases b; congr
  have : b.invFun ≫ (a.toFun ≫ a.invFun) = b.invFun ≫ (b.toFun ≫ b.invFun) := by simp [a.rightInv, b.rightInv]
  rw [h, comp_assoc, comp_assoc, b.leftInv] at this
  simp at this
  assumption

def group : Group (Aut x) := by
  apply Group.ofAxiomsLeft
  case one => exact {
    toFun := 𝟙 _
    invFun := 𝟙 _
    leftInv := by simp
    rightInv := by simp
  }
  case inv =>
    intro h
    exact {
      toFun := h.invFun
      invFun := h.toFun
      leftInv := h.rightInv
      rightInv := h.leftInv
    }
  case mul =>
    intro h g
    exact {
      toFun := h.toFun ≫ g.toFun
      invFun := g.invFun ≫ h.invFun
      leftInv := by
        rw [comp_assoc, ←comp_assoc g.invFun]
        simp [g.leftInv,h.leftInv]
      rightInv := by
        rw [comp_assoc, ←comp_assoc h.toFun]
        simp [g.rightInv, h.rightInv]
    }
  intro x
  ext
  show 𝟙 _ ≫ _ = _
  simp
  intro m
  ext
  apply m.leftInv
  intro a b c
  ext
  symm; apply comp_assoc

instance : GroupOps (Aut x) := group.ops
instance : IsGroup (Aut x) := group.spec

end Category
