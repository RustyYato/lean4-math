import Math.Order.Preorder
import Math.Order.OrderIso

variable [LT α] [LE α] [LT β] [LE β]

def GaloisConnection [IsPreOrder α] [IsPreOrder β] (l: α -> β) (u: β -> α) :=
  ∀a b, l a ≤ b ↔ a ≤ u b

def OrderIso.toGaloisConnection [IsPreOrder α] [IsPreOrder β] (h: α ≃o β): GaloisConnection h.toFun h.invFun := by
  intro a b
  apply Iff.intro
  intro g
  rw [←h.leftInv a]
  apply h.resp_rel.mpr
  rw [h.rightInv, h.rightInv]
  assumption
  intro g
  rw [←h.rightInv b]
  apply h.resp_rel.mp
  assumption

namespace GaloisConnection

section

variable [IsPreOrder α] [IsPreOrder β] {l : α → β} {u : β → α} (gc : GaloisConnection l u)

def le_iff_le {a : α} {b : β} : l a ≤ b ↔ a ≤ u b :=
  gc _ _

def l_le {a : α} {b : β} : a ≤ u b → l a ≤ b :=
  (gc _ _).mpr

def le_u {a : α} {b : β} : l a ≤ b → a ≤ u b :=
  (gc _ _).mp

def le_u_l (a) : a ≤ u (l a) :=
  gc.le_u <| (le_refl _)

def l_u_le (a) : l (u a) ≤ a :=
  gc.l_le <| (le_refl _)

end

end GaloisConnection
