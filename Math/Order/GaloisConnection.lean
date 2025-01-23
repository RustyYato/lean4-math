import Math.Order.Preorder
import Math.Order.OrderIso
import Math.Data.Set.Order.Bounds

variable [LT α] [LE α] [LT β] [LE β] [Sup α] [Sup β] [Inf α] [Inf β] [Top α] [Bot α] [Top β] [Bot β]

def GaloisConnection (l: α -> β) (u: β -> α) :=
  ∀a b, l a ≤ b ↔ a ≤ u b

def OrderIso.toGaloisConnection (h: α ≃o β): GaloisConnection h.toFun h.invFun := by
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

variable {l : α → β} {u : β → α} (gc : GaloisConnection l u)

section PreOrder

variable [IsPreOrder α] [IsPreOrder β]

protected def dual : GaloisConnection
  (Opposite.mk ∘ u ∘ Opposite.get)
  (Opposite.mk ∘ l ∘ Opposite.get) := fun a b => (gc b a).symm

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

def monotone_u : Monotone u := by
  intro x y le
  apply gc.le_u
  apply le_trans
  apply gc.l_u_le
  assumption

def monotone_l : Monotone l :=
  gc.dual.monotone_u.dual

def upperBounds_l_image (gc : GaloisConnection l u) (s : Set α) :
    Set.upperBounds (s.image l) = (Set.upperBounds s).preimage u := by
  ext x
  apply Iff.intro
  intro g
  intro y mem
  apply gc.le_u
  apply g
  apply Set.mem_image'
  assumption
  intro g y ⟨_, _, eq⟩ ; subst eq
  apply gc.l_le
  apply g
  assumption

def lowerBounds_u_image (gc : GaloisConnection l u) (s : Set β) :
    Set.lowerBounds (s.image u) = (Set.lowerBounds s).preimage l :=
  gc.dual.upperBounds_l_image s

def boundedAbove_l_image {s : Set α} : Set.BoundedAbove (s.image l) ↔ Set.BoundedAbove s := by
  apply Iff.intro
  intro ⟨x, hx⟩
  exists u x
  intro y mem
  apply gc.le_u
  apply hx
  apply Set.mem_image'
  assumption
  apply gc.monotone_l.map_bounded_above

def bddBelow_u_image {s : Set β} : Set.BoundedBelow (s.image u) ↔ Set.BoundedBelow s :=
  gc.dual.boundedAbove_l_image

def le_u_l_trans {x y z : α} (hxy : x ≤ u (l y)) (hyz : y ≤ u (l z)) : x ≤ u (l z) :=
  le_trans hxy (gc.monotone_u <| gc.l_le hyz)

def l_u_le_trans {x y z : β} (hxy : l (u x) ≤ y) (hyz : l (u y) ≤ z) : l (u x) ≤ z :=
  le_trans (gc.monotone_l <| gc.le_u hxy) hyz

end PreOrder

section IsPartialOrder

variable [IsPartialOrder α] [IsPreOrder β]

def u_l_u_eq_u (b : β) : u (l (u b)) = u b := by
  apply le_antisymm
  apply gc.monotone_u
  apply gc.l_u_le
  apply gc.le_u
  rfl

def u_unique {l' : α → β} {u' : β → α} (gc' : GaloisConnection l' u') (hl : ∀ a, l a = l' a)
    {b : β} : u b = u' b :=
  le_antisymm (gc'.le_u <| hl (u b) ▸ gc.l_u_le _) (gc.le_u <| (hl (u' b)).symm ▸ gc'.l_u_le _)

def u_eq (gc : GaloisConnection l u) {z : α} {y : β} : u y = z ↔ ∀ x, x ≤ z ↔ l x ≤ y := by
  apply Iff.intro
  intro h x
  rw [←h, gc]
  intro h
  apply le_antisymm
  apply (h _).mpr
  apply gc.l_u_le
  apply gc.le_u
  apply (h _).mp
  rfl

end IsPartialOrder

section IsPartialOrder

variable [IsPreOrder α] [IsPartialOrder β]

def l_u_l_eq_l (a : α) : l (u (l a)) = l a :=
  gc.dual.u_l_u_eq_u _

def l_unique {l' : α → β} {u' : β → α} (gc' : GaloisConnection l' u') (hu : ∀ b, u b = u' b)
    {a : α} : l a = l' a := gc.dual.u_unique gc'.dual hu

def l_eq {x : α} {z : β} : l x = z ↔ ∀ y, z ≤ y ↔ x ≤ u y := gc.dual.u_eq

end IsPartialOrder

section LawfuTop

variable [IsPartialOrder α] [IsPreOrder β] [IsLawfulTop α] [IsLawfulTop β]

def u_eq_top {x} : u x = ⊤ ↔ l ⊤ ≤ x := by
  rw [gc.u_eq]
  simp [le_top]
  apply Iff.intro
  intro h
  apply h
  intro h y
  apply le_trans _ h
  apply gc.monotone_l
  apply le_top

def u_top : u ⊤ = ⊤ := gc.u_eq_top.mpr (le_top _)

end LawfuTop

section LawfuTop

variable [IsPreOrder α] [IsPartialOrder β] [IsLawfulBot α] [IsLawfulBot β]

def l_eq_bot {x} : l x = ⊥ ↔ x ≤ u ⊥ := gc.dual.u_eq_top

def l_bot : l ⊥ = ⊥ := gc.dual.u_top

end LawfuTop

section SemiLatticeSup

variable [IsSemiLatticeSup α] [IsSemiLatticeSup β]

def l_sup : l (a₁ ⊔ a₂) = l a₁ ⊔ l a₂ := by
  apply le_antisymm
  apply gc.l_le
  rw [sup_le_iff]
  apply And.intro
  apply gc.le_u
  apply le_sup_left
  apply gc.le_u
  apply le_sup_right
  rw [sup_le_iff]
  apply And.intro
  apply gc.monotone_l
  apply le_sup_left
  apply gc.monotone_l
  apply le_sup_right

end SemiLatticeSup

section SemiLatticeInf

variable [IsSemiLatticeInf α] [IsSemiLatticeInf β]

def u_inf : u (a₁ ⊓ a₂) = u a₁ ⊓ u a₂ := gc.dual.l_sup

end SemiLatticeInf

end GaloisConnection
