import Math.Order.OrderIso
import Math.Data.Set.Order.Bounds
import Math.Order.Lattice.Complete

variable {α β : Type*} [LT α] [LE α] [LT β] [LE β]

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

def monotoneIntro (hu : Monotone u) (hl : Monotone l) (hul : ∀ a, a ≤ u (l a))
    (hlu : ∀ a, l (u a) ≤ a) : GaloisConnection l u := by
  intro a b
  apply Iff.intro
  intro h
  apply le_trans (hul _)
  apply hu
  assumption
  intro h
  apply le_trans (hl _)
  apply hlu
  assumption

def dual : GaloisConnection
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

section LawfulTop

variable [IsPartialOrder α] [IsPreOrder β] [Top α] [Top β] [IsLawfulTop α] [IsLawfulTop β]

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

abbrev instLawfulTop (gc : GaloisConnection l u) : LawfulTop α where
  top := u ⊤
  le_top x := by
    show _ ≤ u ⊤
    apply gc.le_u
    apply le_top

end LawfulTop

section LawfulBot

variable [IsPreOrder α] [IsPartialOrder β] [Bot α] [Bot β] [IsLawfulBot α] [IsLawfulBot β]

def l_eq_bot {x} : l x = ⊥ ↔ x ≤ u ⊥ := gc.dual.u_eq_top

def l_bot : l ⊥ = ⊥ := gc.dual.u_top

abbrev instLawfulBot (gc : GaloisConnection l u) : LawfulBot β where
  bot := l ⊥
  bot_le x := by
    show l ⊥ ≤ _
    apply gc.l_le
    apply bot_le

end LawfulBot

section SemiLatticeMax

variable [Max α] [Max β] [IsSemiLatticeMax α] [IsSemiLatticeMax β]

def l_max : l (a₁ ⊔ a₂) = l a₁ ⊔ l a₂ := by
  apply le_antisymm
  apply gc.l_le
  rw [max_le_iff]
  apply And.intro
  apply gc.le_u
  apply le_max_left
  apply gc.le_u
  apply le_max_right
  rw [max_le_iff]
  apply And.intro
  apply gc.monotone_l
  apply le_max_left
  apply gc.monotone_l
  apply le_max_right

end SemiLatticeMax

section SemiLatticeMin

variable [Min α] [Min β] [IsSemiLatticeMin α] [IsSemiLatticeMin β]

def u_min : u (a₁ ⊓ a₂) = u a₁ ⊓ u a₂ := gc.dual.l_max

end SemiLatticeMin

end GaloisConnection

structure GaloisInsertion (l : α → β) (u : β → α) where
  gc : GaloisConnection l u
  le_l_u : ∀ x, x ≤ l (u x)
  choice : ∀ x : α, u (l x) ≤ x → β := fun x _ => l x
  choice_eq : ∀ a h, choice a h = l a := by intros; rfl

structure GaloisCoinsertion (l : α → β) (u : β → α) where
  gc : GaloisConnection l u
  u_l_le : ∀ x, u (l x) ≤ x
  choice : ∀ x : β, x ≤ l (u x) → α
  choice_eq : ∀ a h, choice a h = u a

section GaloisInsertion

variable [IsPreOrder α] [IsPreOrder β]  {l : α → β} {u : β → α}

abbrev GaloisInsertion.dual (gi: GaloisInsertion l u) : GaloisCoinsertion
  (Opposite.mk ∘ u ∘ Opposite.get)
  (Opposite.mk ∘ l ∘ Opposite.get) where
  choice := gi.choice
  gc := gi.gc.dual
  u_l_le := gi.le_l_u
  choice_eq := gi.choice_eq

abbrev GaloisCoinsertion.dual (gi: GaloisCoinsertion l u) : GaloisInsertion
  (Opposite.mk ∘ u ∘ Opposite.get)
  (Opposite.mk ∘ l ∘ Opposite.get) where
  choice := gi.choice
  gc := gi.gc.dual
  le_l_u := gi.u_l_le
  choice_eq := gi.choice_eq

def GaloisInsertion.isLUB_of_u_image (gi : GaloisInsertion l u) {s : Set β} {a : α}
    (hs : (s.image u).IsLUB a) : s.IsLUB (l a) := by
  apply And.intro
  intro x hx
  apply le_trans (gi.le_l_u x)
  apply gi.gc.monotone_l
  apply hs.left
  apply Set.mem_image'
  assumption
  intro x hx
  apply gi.gc.l_le
  apply hs.right
  intro _ ⟨y, hy, eq⟩ ; subst eq
  apply gi.gc.monotone_u
  apply hx
  assumption

def GaloisInsertion.isGLB_of_u_image (gi : GaloisInsertion l u) {s : Set β} {a : α}
    (hs : (s.image u).IsGLB a) : s.IsGLB (l a) := by
  apply And.intro
  intro x hx
  apply gi.gc.l_le
  apply hs.left
  apply Set.mem_image'
  assumption
  intro b hb
  apply le_trans
  apply gi.le_l_u
  apply gi.gc.monotone_l
  apply hs.right
  intro _ ⟨c, hc, eq⟩; subst eq
  apply gi.gc.monotone_u
  apply hb
  assumption

abbrev GaloisInsertion.monotoneIntro (hu : Monotone u) (hl : Monotone l) (hul : ∀ a, a ≤ u (l a)) (hlu : ∀ b, l (u b) = b) : GaloisInsertion l u where
  gc := .monotoneIntro hu hl hul (fun x => le_of_eq (hlu x))
  le_l_u := fun x => by rw [hlu]

/-- Makes a Galois insertion from an order-preserving bijection. -/
abbrev OrderIso.toGaloisInsertion (oi : α ≃o β) :
    GaloisInsertion oi oi.symm where
  gc := oi.toGaloisConnection
  le_l_u g := le_of_eq (oi.rightInv g).symm

/-- Make a `GaloisInsertion l u` from a `GaloisConnection l u` such that `∀ b, b ≤ l (u b)` -/
abbrev GaloisConnection.toGaloisInsertion (gc : GaloisConnection l u) (h : ∀ b, b ≤ l (u b)) : GaloisInsertion l u where
  gc := gc
  le_l_u := h

abbrev GaloisInsertion.instLawfulTop [Top α] [IsLawfulTop α] (gi : GaloisInsertion l u) : LawfulTop β where
  top := gi.choice ⊤ (le_top _)
  le_top x := by
    show _ ≤ gi.choice ⊤ (le_top _)
    rw [gi.choice_eq]
    apply le_trans
    apply gi.le_l_u
    apply gi.gc.monotone_l
    apply le_top

abbrev GaloisCoinsertion.instLawfulBot [Bot β] [IsLawfulBot β] (gi : GaloisCoinsertion l u) : LawfulBot α :=
    have := gi.dual.instLawfulTop
    inferInstanceAs (LawfulBot αᵒᵖᵒᵖ)

abbrev GaloisInsertion.instLawfulSup [Max α] [IsLawfulMax α] (gi: GaloisInsertion l u) : LawfulSup β where
  max a b := l (u a ⊔ u b)
  le_max_left := by
    intro x y
    show x ≤ l _
    apply le_trans
    apply gi.le_l_u
    apply gi.gc.monotone_l
    apply le_max_left
  le_max_right := by
    intro x y
    show y ≤ l _
    apply le_trans
    apply gi.le_l_u
    apply gi.gc.monotone_l
    apply le_max_right

abbrev GaloisCoinsertion.instLawfulInf [Min β] [IsLawfulMin β] [IsPreOrder β] (gi: GaloisCoinsertion l u) : LawfulInf α :=
  have := gi.dual.instLawfulSup (β := αᵒᵖ) (α := βᵒᵖ)
  inferInstanceAs (LawfulInf αᵒᵖᵒᵖ)

abbrev GaloisInsertion.instSemilatticeSup [Max α] [IsPartialOrder β] [IsSemiLatticeMax α] (gi: GaloisInsertion l u) : SemiLatticeMax β where
  max a b := l (u a ⊔ u b)
  le_max_left := by
    intro x y
    apply le_trans
    apply gi.le_l_u
    apply gi.gc.monotone_l
    apply le_max_left
  le_max_right := by
    intro x y
    apply le_trans
    apply gi.le_l_u
    apply gi.gc.monotone_l
    apply le_max_right
  max_le := by
    intro a b k ka kb
    apply gi.gc.l_le
    apply max_le
    apply gi.gc.monotone_u
    assumption
    apply gi.gc.monotone_u
    assumption

abbrev GaloisInsertion.instSemilatticeInf [Min α] [IsPartialOrder β] [IsSemiLatticeMin α] (gi: GaloisInsertion l u) : SemiLatticeMin β where
  min a b := gi.choice (u a ⊓ u b) (by
    apply le_min
    apply gi.gc.monotone_u
    apply gi.gc.l_le
    apply min_le_left
    apply gi.gc.monotone_u
    apply gi.gc.l_le
    apply min_le_right)
  min_le_left := by
    intro x y
    show gi.choice _ _ ≤ _
    rw [gi.choice_eq]
    apply gi.gc.l_le
    apply min_le_left
  min_le_right := by
    intro x y
    show gi.choice _ _ ≤ _
    rw [gi.choice_eq]
    apply gi.gc.l_le
    apply min_le_right
  le_min := by
    intro a b k ka kb
    show _ ≤ gi.choice _ _
    rw [gi.choice_eq]
    apply le_trans
    apply gi.le_l_u
    apply gi.gc.monotone_l
    apply le_min
    apply gi.gc.monotone_u
    assumption
    apply gi.gc.monotone_u
    assumption

abbrev GaloisCoinsertion.instSemilatticeSup [Max β] [IsPartialOrder α] [IsSemiLatticeMax β] (gi: GaloisCoinsertion l u) : SemiLatticeMax α :=
  have := gi.dual.instSemilatticeInf (β := αᵒᵖ) (α := βᵒᵖ)
  inferInstanceAs (SemiLatticeMax αᵒᵖᵒᵖ)

abbrev GaloisCoinsertion.instSemilatticeInf [Min β] [IsPartialOrder α] [IsSemiLatticeMin β] (gi: GaloisCoinsertion l u) : SemiLatticeMin α :=
  have := gi.dual.instSemilatticeSup (β := αᵒᵖ) (α := βᵒᵖ)
  inferInstanceAs (SemiLatticeMin αᵒᵖᵒᵖ)

abbrev GaloisInsertion.instLattice [Min α] [Max α] [IsPartialOrder β] [IsLattice α] (gi: GaloisInsertion l u) : Lattice β :=
  have := gi.instSemilatticeSup
  have := gi.instSemilatticeInf
  inferInstance

abbrev GaloisCoinsertion.instLattice [Min β] [Max β] [IsPartialOrder α] [IsLattice β] (gi: GaloisCoinsertion l u) : Lattice α :=
  have := gi.instSemilatticeSup
  have := gi.instSemilatticeInf
  inferInstance

abbrev GaloisInsertion.liftCompleteLattice
  [Max α] [Min α] [SupSet α] [InfSet α] [Top α] [Bot α] [IsCompleteLattice α]
  [IsPartialOrder β] (gi : GaloisInsertion l u) : CompleteLattice β :=
  { gi.instLawfulTop, gi.gc.instLawfulBot, gi.instLattice with
    sSup := fun s => l (sSup (s.image u))
    sSup_le := fun s _ => by apply (gi.isLUB_of_u_image (isLUB_sSup _)).2
    le_sSup := fun s => by
      apply (gi.isLUB_of_u_image (isLUB_sSup _)).1
      assumption
    sInf s :=  by
      apply gi.choice (sInf (s.image u))
      apply (isGLB_sInf _).right
      apply gi.gc.monotone_u.mem_lowerBounds_image
      intro b hb
      apply gi.gc.l_le
      apply (isGLB_sInf _).left
      apply Set.mem_image'
      assumption
    sInf_le s := by
      dsimp; rw [gi.choice_eq]
      apply (gi.isGLB_of_u_image (isGLB_sInf _)).left
      assumption
    le_sInf s _ := by
      dsimp; rw [gi.choice_eq]
      apply (gi.isGLB_of_u_image (isGLB_sInf _)).right }

end GaloisInsertion
