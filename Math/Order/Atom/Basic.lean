import Math.Order.Partial
import Math.Logic.Nontrivial

section IsAtom

variable [Bot α] [LE α] [LT α] [IsPartialOrder α] [IsLawfulBot α] {x a: α}

-- if a is the smallest element larger than bot
def IsAtom (a: α) := a ≠ ⊥ ∧ ∀b < a, b = ⊥

def IsAtom.lt_iff (h : IsAtom a) : x < a ↔ x = ⊥ := by
  apply Iff.intro
  apply h.right
  intro h; subst h
  apply lt_of_le_of_ne
  apply bot_le
  symm; apply h.left

def IsAtom.le_iff (h : IsAtom a) : x ≤ a ↔ x = ⊥ ∨ x = a := by
  rw [le_iff_lt_or_eq, h.lt_iff]

end IsAtom

section IsAtom

variable [Top α] [LE α] [LT α] [IsPartialOrder α] [IsLawfulTop α] {x a: α}

-- if a is the largest element smaller than top
def IsCoatom (a: α) := a ≠ ⊤ ∧ ∀b > a, b = ⊤

def IsCoatom.gt_iff (h : IsCoatom a) : a < x ↔ x = ⊤ :=
  IsAtom.lt_iff (α := αᵒᵖ ) h

def IsCoatom.ge_iff (h : IsCoatom a) : a ≤ x ↔ x = ⊤ ∨ x = a :=
  IsAtom.le_iff (α := αᵒᵖ) h

end IsAtom

class IsAtomic (α: Type*) [Bot α] [LE α] [LT α] where
  exists_atom_of_ne_bot : ∀x: α, x ≠ ⊥ -> ∃y: α, IsAtom y ∧ y ≤ x

class IsCoatomic (α: Type*) [Top α] [LE α] [LT α] where
  exists_coatom_of_ne_top : ∀x: α, x ≠ ⊤ -> ∃y: α, IsCoatom y ∧ x ≤ y

def exists_atom_of_ne_bot [Bot α] [LE α] [LT α] [IsAtomic α] : ∀x: α, x ≠ ⊥ -> ∃y: α, IsAtom y ∧ y ≤ x :=
  IsAtomic.exists_atom_of_ne_bot

def exists_coatom_of_ne_top [Top α] [LE α] [LT α] [IsCoatomic α] : ∀x: α, x ≠ ⊤ -> ∃y: α, IsCoatom y ∧ x ≤ y :=
  IsCoatomic.exists_coatom_of_ne_top

instance [Bot α] [LE α] [LT α] [IsAtomic α] : IsCoatomic αᵒᵖ where
  exists_coatom_of_ne_top := exists_atom_of_ne_bot (α := α)
instance [Top α] [LE α] [LT α] [IsCoatomic α] : IsAtomic αᵒᵖ where
  exists_atom_of_ne_bot := exists_coatom_of_ne_top (α := α)

def exists_atom [Bot α] [LE α] [LT α] [IsLawfulBot α] [IsNontrivial α] [IsAtomic α] : ∃ a : α, IsAtom a := by
  have ⟨x, hx⟩ := exists_ne (⊥: α)
  have ⟨y,_, _⟩  := exists_atom_of_ne_bot _ hx
  exists y

def exists_coatom [Top α] [LE α] [LT α] [IsLawfulTop α] [IsNontrivial α] [IsCoatomic α] := exists_atom (α := αᵒᵖ)
