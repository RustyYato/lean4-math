import Math.Order.Partial
import Math.Order.Notation
import Math.Order.TopBot

variable (α: Type*) [LE α] [LT α]
variable {α₀: Type*} [Sup α₀] [Inf α₀] [LE α₀] [LT α₀]

class IsSemiLatticeSup  [Sup α] extends IsLawfulSup α, IsPartialOrder α: Prop where
  sup_le: ∀{a b k: α}, a ≤ k -> b ≤ k -> a ⊔ b ≤ k

class IsSemiLatticeInf [Inf α] extends IsLawfulInf α, IsPartialOrder α: Prop where
  le_inf: ∀{a b k: α}, k ≤ a -> k ≤ b -> k ≤ a ⊓ b

class IsLattice [Sup α] [Inf α] extends IsSemiLatticeSup α, IsSemiLatticeInf α, IsPartialOrder α: Prop where

class SemiLatticeSup extends LawfulSup α, IsPartialOrder α where
  sup_le: ∀{a b k: α}, a ≤ k -> b ≤ k -> a ⊔ b ≤ k

class SemiLatticeInf extends LawfulInf α, IsPartialOrder α where
  le_inf: ∀{a b k: α}, k ≤ a -> k ≤ b -> k ≤ a ⊓ b

class Lattice extends SemiLatticeSup α, SemiLatticeInf α where
  mk' ::

export IsSemiLatticeSup (sup_le)
export IsSemiLatticeInf (le_inf)

instance [Sup α] [IsSemiLatticeSup α] : IsSemiLatticeInf αᵒᵖ where
  le_inf := sup_le (α := α)

instance [Inf α] [IsSemiLatticeInf α] : IsSemiLatticeSup αᵒᵖ where
  sup_le := le_inf (α := α)

instance [Sup α] [Inf α] [IsLattice α] : IsLattice αᵒᵖ where
  toIsSemiLatticeSup := inferInstance
  inf_le_left := inf_le_left
  inf_le_right := inf_le_right
  le_inf := le_inf

instance [h: SemiLatticeSup α] : IsSemiLatticeSup α where
  sup_le := h.sup_le

instance [h: SemiLatticeInf α] : IsSemiLatticeInf α where
  le_inf := h.le_inf

instance [SemiLatticeSup α] : SemiLatticeInf αᵒᵖ where
  le_inf := sup_le (α := α)

instance [SemiLatticeInf α] : SemiLatticeSup αᵒᵖ where
  sup_le := le_inf (α := α)

instance [Lattice α] : IsLattice α where
  le_inf := le_inf

instance [Lattice α] : Lattice αᵒᵖ where
  le_inf := le_inf

instance [h: SemiLatticeSup α] [g: SemiLatticeInf α] : Lattice α where
  le_inf := g.le_inf

attribute [simp] le_sup_left le_sup_right
attribute [simp] inf_le_left inf_le_right

variable (α: Type*) [Sup α] [Inf α] [LE α] [LT α]

section

variable [IsSemiLatticeSup α₀]

@[simp]
def sup_le_iff : ∀{a b k: α₀}, a ⊔ b ≤ k ↔ a ≤ k ∧ b ≤ k := by
  intro a b k
  apply Iff.intro
  intro h
  apply And.intro
  apply le_trans _ h
  simp
  apply le_trans _ h
  simp
  simp
  exact sup_le

def sup_idemp: ∀a: α₀, a ⊔ a = a := by
  intro a
  apply le_antisymm <;> simp

def sup_comm: ∀a b: α₀, a ⊔ b = b ⊔ a := by
  intro a b
  apply le_antisymm <;> simp

def sup_assoc: ∀a b c: α₀, a ⊔ b ⊔ c = a ⊔ (b ⊔ c) := by
  intro a b c
  apply le_antisymm <;> simp
  apply And.intro
  apply le_trans _ (le_sup_right _ _)
  simp
  apply le_trans _ (le_sup_right _ _)
  simp
  apply And.intro
  apply le_trans _ (le_sup_left _ _)
  simp
  apply le_trans _ (le_sup_left _ _)
  simp

instance : @Std.Commutative α₀ (· ⊔ ·) := ⟨sup_comm⟩
instance : @Std.Associative α₀ (· ⊔ ·) := ⟨sup_assoc⟩
instance : @Std.IdempotentOp α₀ (· ⊔ ·) := ⟨sup_idemp⟩

def of_sup_eq_right {a b: α₀} : a ⊔ b = b -> a ≤ b := by
  intro h
  rw [←h]
  simp
def of_sup_eq_left {a b: α₀} : a ⊔ b = a -> b ≤ a := by
  intro h
  rw [←h]
  simp

def sup_eq_right {a b: α₀} : a ⊔ b = b ↔ a ≤ b := by
  apply Iff.intro
  apply of_sup_eq_right
  intro h
  apply le_antisymm
  apply sup_le <;> trivial
  simp
def sup_eq_left {a b: α₀} : a ⊔ b = a ↔ b ≤ a := by
  rw [sup_comm]
  apply sup_eq_right

def lt_sup_left {a b k: α₀} : k < a -> k < a ⊔ b := by
  simp [lt_iff_le_and_not_le]
  intro ka nak
  apply And.intro
  apply le_trans
  assumption
  apply le_sup_left
  intro ak
  contradiction

def lt_sup_right {a b k: α₀} : k < b -> k < a ⊔ b := by
  rw [sup_comm]
  apply lt_sup_left

def sup_le_sup {a b c d: α₀} :
  a ≤ c ->
  b ≤ d ->
  a ⊔ b ≤ c ⊔ d := by
  intro ac bd
  apply sup_le
  apply le_trans _ (le_sup_left _ _)
  assumption
  apply le_trans _ (le_sup_right _ _)
  assumption

variable [Top α₀] [Bot α₀] [IsLawfulBot α₀] [IsLawfulTop α₀]
variable {a: α₀}

@[simp]
def bot_sup : ⊥ ⊔ a = a := by
  apply le_antisymm
  apply sup_le
  apply bot_le
  rfl
  simp

@[simp]
def sup_bot : a ⊔ ⊥ = a := by
  simp [sup_comm a]

@[simp]
def top_sup : ⊤ ⊔ a = ⊤ := by
  apply le_antisymm
  apply sup_le
  rfl
  apply le_top
  simp

@[simp]
def sup_top : a ⊔ ⊤ = ⊤ := by
  simp [sup_comm a]

end

section

variable [IsSemiLatticeInf α₀]

@[simp]
def le_inf_iff : ∀{a b k: α₀}, k ≤ a ⊓ b ↔ k ≤ a ∧ k ≤ b :=
  sup_le_iff (α₀ := Opposite α₀)

def inf_idemp: ∀a: α₀, a ⊓ a = a :=
  sup_idemp (α₀ := Opposite α₀)

def inf_comm: ∀a b: α₀, a ⊓ b = b ⊓ a :=
  sup_comm (α₀ := Opposite α₀)

def inf_assoc: ∀a b c: α₀, a ⊓ b ⊓ c = a ⊓ (b ⊓ c) :=
  sup_assoc (α₀ := Opposite α₀)

instance : @Std.Commutative α₀ (· ⊓ ·) := ⟨inf_comm⟩
instance : @Std.Associative α₀ (· ⊓ ·) := ⟨inf_assoc⟩
instance : @Std.IdempotentOp α₀ (· ⊓ ·) := ⟨inf_idemp⟩

def of_inf_eq_right {a b: α₀} : a ⊓ b = b -> b ≤ a :=
  of_sup_eq_right (α₀ := Opposite α₀)
def of_inf_eq_left {a b: α₀} : a ⊓ b = a -> a ≤ b :=
  of_sup_eq_left (α₀ := Opposite α₀)

def inf_eq_right {a b: α₀} : a ⊓ b = b ↔ b ≤ a :=
  sup_eq_right (α₀ := Opposite α₀)
def inf_eq_left {a b: α₀} : a ⊓ b = a ↔ a ≤ b :=
  sup_eq_left (α₀ := Opposite α₀)

def inf_le_inf {a b c d: α₀} :
  a ≤ c -> b ≤ d -> a ⊓ b ≤ c ⊓ d := sup_le_sup (α₀ := α₀ᵒᵖ)

variable [Top α₀] [Bot α₀] [IsLawfulBot α₀] [IsLawfulTop α₀]
variable {a: α₀}

@[simp]
def bot_inf : ⊥ ⊓ a = ⊥ :=
  top_sup (α₀ := Opposite α₀)

@[simp]
def inf_bot : a ⊓ ⊥ = ⊥ :=
  sup_top (α₀ := Opposite α₀)

@[simp]
def top_inf : ⊤ ⊓ a = a :=
  bot_sup (α₀ := Opposite α₀)

@[simp]
def inf_top : a ⊓ ⊤ = a :=
  sup_bot (α₀ := Opposite α₀)

end

section

variable [IsLattice α₀]

def inf_le_sup (a b: α₀) : a ⊓ b ≤ a ⊔ b :=
  le_trans (inf_le_left _ _) (le_sup_left _ _)

def inf_sup_self (a b: α₀) : a ⊓ (a ⊔ b) = a := by apply le_antisymm <;> simp
def sup_inf_self (a b: α₀) : a ⊔ (a ⊓ b) = a := by apply le_antisymm <;> simp

def sup_eq_iff_inf_eq {a b: α₀} : a ⊔ b = a ↔ a ⊓ b = b := by
  rw [sup_eq_left, inf_eq_right]

end

class IsDistribLattice extends IsLattice α where
  le_sup_inf : ∀{x y z : α}, (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z

section

variable [IsDistribLattice α₀]

theorem le_sup_inf : ∀ {x y z : α₀}, (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z :=
  IsDistribLattice.le_sup_inf

end

namespace OrderIso

def instIsSemiLatticeSup
  {α}
  [LE α] [LT α] [Sup α]
  [LE β] [LT β] [Sup β]
  [IsSemiLatticeSup α]
  [_root_.IsPartialOrder β]
  (h: β ≃o α)
  (hs: ∀a b, h (a ⊔ b) = h a ⊔ h b): IsSemiLatticeSup β where
  le_sup_left := by
    intro a b
    have : h a ≤ h a ⊔ h b := le_sup_left _ _
    rw [←hs] at this
    exact h.resp_le.mpr this
  le_sup_right := by
    intro a b
    have : h b ≤ h a ⊔ h b := le_sup_right _ _
    rw [←hs] at this
    exact h.resp_le.mpr this
  sup_le := by
    intro a b k ak bk
    replace ak := h.resp_le.mp ak
    replace bk := h.resp_le.mp bk
    have := sup_le ak bk
    rw [←hs] at this
    exact h.resp_le.mpr this

def instIsSemiLatticeInf
  {α}
  [LE α] [LT α] [Inf α]
  [LE β] [LT β] [Inf β]
  [IsSemiLatticeInf α]
  [_root_.IsPartialOrder β]
  (h: β ≃o α)
  (hs: ∀a b, h (a ⊓ b) = h a ⊓ h b): IsSemiLatticeInf β where
  inf_le_left := by
    intro a b
    have : h a ⊓ h b ≤ h a := inf_le_left _ _
    rw [←hs] at this
    exact h.resp_le.mpr this
  inf_le_right := by
    intro a b
    have : h a ⊓ h b ≤ h b := inf_le_right _ _
    rw [←hs] at this
    exact h.resp_le.mpr this
  le_inf := by
    intro a b k ak bk
    replace ak := h.resp_le.mp ak
    replace bk := h.resp_le.mp bk
    have := le_inf ak bk
    rw [←hs] at this
    exact h.resp_le.mpr this

end OrderIso

instance [LE α] [LT α] [Sup α] [IsSemiLatticeSup α] : IsSemiLatticeSup (WithTop α) where
  le_sup_left := by
    intro a b
    cases a <;> cases b
    any_goals rfl
    apply WithTop.LE.top
    apply WithTop.LE.of
    apply le_sup_left
  le_sup_right := by
    intro a b
    cases a <;> cases b
    any_goals rfl
    apply WithTop.LE.top
    apply WithTop.LE.of
    apply le_sup_right
  sup_le := by
    intro a b k ak bk
    cases ak <;> cases bk
    apply WithTop.LE.top
    apply WithTop.LE.of
    apply sup_le <;> assumption

instance [LE α] [LT α] [Inf α] [IsSemiLatticeInf α] : IsSemiLatticeInf (WithTop α) where
  inf_le_left := by
    intro a b
    cases a <;> cases b
    any_goals rfl
    apply WithTop.LE.top
    apply WithTop.LE.of
    apply inf_le_left
  inf_le_right := by
    intro a b
    cases a <;> cases b
    any_goals rfl
    apply WithTop.LE.top
    apply WithTop.LE.of
    apply inf_le_right
  le_inf := by
    intro a b k ak bk
    cases ak <;> cases bk
    apply WithTop.LE.top
    apply WithTop.LE.of
    assumption
    apply WithTop.LE.of
    assumption
    apply WithTop.LE.of
    apply le_inf <;> assumption

instance [LE α] [LT α] [Sup α] [IsSemiLatticeSup α] : IsSemiLatticeSup (WithBot α) :=
  WithBot.orderIsoWithTop.instIsSemiLatticeSup <| by
    intro a b
    cases a <;> cases b
    all_goals rfl

instance [LE α] [LT α] [Inf α] [IsSemiLatticeInf α] : IsSemiLatticeInf (WithBot α) :=
  WithBot.orderIsoWithTop.instIsSemiLatticeInf <| by
    intro a b
    cases a <;> cases b
    all_goals rfl

instance [LE α] [LT α] [Inf α] [IsLattice α] : IsLattice (WithTop α) where
  inf_le_left := inf_le_left
  inf_le_right := inf_le_right
  le_inf := le_inf

instance [LE α] [LT α] [Inf α] [IsLattice α] : IsLattice (WithBot α) where
  inf_le_left := inf_le_left
  inf_le_right := inf_le_right
  le_inf := le_inf
