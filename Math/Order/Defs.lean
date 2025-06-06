import Math.Logic.Basic
import Math.Order.Notation
import Math.Relation.Defs
import Math.Data.Opposite

class OrderOps (α: Type*) extends LE α, LT α where

class LatticeOps (α: Type*) extends OrderOps α, Min α, Max α where

instance [LE α] [LT α] : OrderOps α where
instance [LE α] [LT α] [Min α] [Max α] : LatticeOps α where

class IsPreOrder (α: Type*) [LT α] [LE α] : Prop extends IsLawfulLT α where
  le_refl: ∀a: α, a ≤ a
  le_trans: ∀{a b c: α}, a ≤ b -> b ≤ c -> a ≤ c

class IsPartialOrder (α: Type*) [LT α] [LE α] : Prop extends IsPreOrder α where
  le_antisymm: ∀{a b: α}, a ≤ b -> b ≤ a -> a = b

class IsLinearOrder (α: Type*) [LT α] [LE α] : Prop extends IsLawfulLT α where
  le_antisymm: ∀{a b: α}, a ≤ b -> b ≤ a -> a = b
  lt_or_le: ∀a b: α, a < b ∨ b ≤ a
  le_trans: ∀{a b c: α}, a ≤ b -> b ≤ c -> a ≤ c

instance [LT α] [LE α] [IsLinearOrder α] : IsPartialOrder α where
  le_antisymm := IsLinearOrder.le_antisymm
  le_refl := by
    intro a
    rcases IsLinearOrder.lt_or_le a a with r | r
    exact (lt_iff_le_and_not_le.mp r).left
    assumption
  le_trans := IsLinearOrder.le_trans

class IsSemiLatticeMax (α: Type*) [LE α] [LT α]  [Max α] : Prop extends IsLawfulMax α, IsPartialOrder α where
  max_le: ∀{a b k: α}, a ≤ k -> b ≤ k -> a ⊔ b ≤ k

class IsSemiLatticeMin (α: Type*) [LE α] [LT α] [Min α] : Prop extends IsLawfulMin α, IsPartialOrder α where
  le_min: ∀{a b k: α}, k ≤ a -> k ≤ b -> k ≤ a ⊓ b

class IsLattice (α: Type*) [LE α] [LT α] [Max α] [Min α] : Prop extends IsSemiLatticeMax α, IsSemiLatticeMin α, IsPartialOrder α where

class IsLinearLattice (α: Type*) [LT α] [LE α] [Min α] [Max α] : Prop extends IsLinearOrder α, IsLattice α where

class IsDecidableLinearOrder (α: Type _) [LE α] [LT α] [Min α] [Max α] extends IsLinearLattice α where
  decLE (a b: α): Decidable (a ≤ b) := by intros; exact inferInstance
  decLT (a b: α): Decidable (a < b) := decidable_of_iff _ (lt_iff_le_and_not_le (a := a) (b := b)).symm
  decEQ (a b: α): Decidable (a = b) := decidable_of_iff (a ≤ b ∧ b ≤ a) (by
  apply Iff.intro
  · rintro ⟨ab,ba⟩
    apply le_antisymm ab ba
  · intro h
    subst h
    apply And.intro <;> apply IsPreOrder.le_refl)
  min_def (a b: α): min a b = if a ≤ b then a else b := by intros; rfl
  max_def (a b: α): max a b = if a ≤ b then b else a := by intros; rfl

section IsPreOrder

variable [LT α] [LE α] [IsPreOrder α] {a b c: α}

@[refl, simp]
def le_refl: ∀a: α, a ≤ a := IsPreOrder.le_refl
def le_trans: a ≤ b -> b ≤ c -> a ≤ c := IsPreOrder.le_trans

instance : @Relation.IsTrans α (· ≤ ·) where
  trans := le_trans
instance : @Relation.IsRefl α (· ≤ ·) where
  refl := le_refl
instance : @Relation.IsTrans α (· < ·) := inferInstance
instance : @Relation.IsIrrefl α (· < ·) := inferInstance
instance : @Trans α α α (· < ·) (· ≤ ·) (· < ·) := inferInstance
instance : @Trans α α α (· < ·) (· ≤ ·) (· < ·) := inferInstance
instance : @Trans α α α (· < ·) (· < ·) (· < ·) := inferInstance
instance : @Trans α α α (· ≤ ·) (· ≤ ·) (· ≤ ·) := inferInstance

def le_of_lt: a < b -> a ≤ b := fun h => (lt_iff_le_and_not_le.mp h).left
def lt_of_le_of_not_le : a ≤ b -> ¬(b ≤ a) -> a < b := (lt_iff_le_and_not_le.mpr ⟨·, ·⟩)

def le_of_eq: a = b -> a ≤ b := fun h => h ▸ le_refl _
def not_le_of_lt (hab : a < b) : ¬ b ≤ a := (lt_iff_le_and_not_le.1 hab).2
def not_lt_of_le (hab : a ≤ b) : ¬ b < a := imp_not_comm.1 not_le_of_lt hab
def lt_irrefl: ¬a < a := fun h => (lt_iff_le_and_not_le.mp h).right (le_refl _)
def ne_of_lt: a < b -> a ≠ b := fun h g => lt_irrefl (g ▸ h)
def le_of_lt_or_eq: a < b ∨ a = b -> a ≤ b := by
  intro h
  cases h
  apply le_of_lt; assumption
  apply le_of_eq; assumption
def lt_trans : a < b -> b < c -> a < c := trans
def lt_of_lt_of_le : a < b -> b ≤ c -> a < c := trans
def lt_of_le_of_lt : a ≤ b -> b < c -> a < c := trans

def lt_asymm : a < b -> b < a -> False := (lt_irrefl <| lt_trans · ·)

 instance : @Trans α α α (· < ·) (· ≤ ·) (· < ·) where
  trans := lt_of_lt_of_le
 instance : @Trans α α α (· < ·) (· = ·) (· < ·) where
  trans := lt_of_lt_of_eq

 instance : @Trans α α α (· ≤ ·) (· < ·) (· < ·) where
  trans := lt_of_le_of_lt
 instance : @Trans α α α (· = ·) (· < ·) (· < ·) where
  trans := lt_of_eq_of_lt

instance [IsPreOrder α] : IsPreOrder αᵒᵖ where
  lt_iff_le_and_not_le := lt_iff_le_and_not_le (α := α)
  le_refl := le_refl (α := α)
  le_trans := flip (le_trans (α := α))

end IsPreOrder

section IsPartialOrder

variable [LT α] [LE α] [IsPartialOrder α] {a b c: α}

def le_antisymm: a ≤ b -> b ≤ a -> a = b := IsPartialOrder.le_antisymm

instance : Relation.IsPartialOrder (α := α) (· ≤ ·) (· = ·) where
  antisymm_by := le_antisymm

def le_iff_lt_or_eq: a ≤ b ↔ a < b ∨ a = b := Relation.IsLawfulNonstrict.is_lawful_nonstrict _ _
def lt_or_eq_of_le: a ≤ b -> a < b ∨ a = b := le_iff_lt_or_eq.mp
def lt_of_le_of_ne: a ≤ b -> a ≠ b -> a < b := by
  intro h g
  cases lt_or_eq_of_le h
  assumption
  contradiction

@[simp] def le_bot [Bot α] [IsLawfulBot α] {a: α} : a ≤ ⊥ ↔ a = ⊥ := by
  apply Iff.intro
  intro h
  apply le_antisymm
  assumption
  apply bot_le
  intro h; rw [h]

@[simp] def top_le [Top α] [IsLawfulTop α] {a: α} : ⊤ ≤ a ↔ a = ⊤ := by
  apply Iff.intro
  intro h
  apply le_antisymm
  apply le_top
  assumption
  intro h; rw [h]

instance : @Relation.IsAntisymm α (· ≤ ·) where
  antisymm_by := le_antisymm

instance [IsPartialOrder α] : IsPartialOrder αᵒᵖ where
  le_antisymm := by
    intro a b ab ba
    apply le_antisymm (α := α) <;> assumption

instance (priority := 500) [Relation.IsPreorder (α := α) (· ≤ ·)] : IsPreOrder α := inferInstance

instance (priority := 500) instLOofPOofLTconnected_by [Relation.IsConnected (· < (·: α))] : IsLinearOrder α where
  lt_iff_le_and_not_le := lt_iff_le_and_not_le
  le_antisymm := le_antisymm
  le_trans := le_trans
  lt_or_le := by
    intro a b
    rcases Relation.connected (· < ·) a b with lt | eq | gt
    left; assumption
    right; rw [eq]
    right; apply le_of_lt; assumption

instance (priority := 500) instLOofPOofLEconnected_by [Relation.IsConnected (· ≤ (·: α))] : IsLinearOrder α where
  lt_iff_le_and_not_le := lt_iff_le_and_not_le
  le_antisymm := le_antisymm
  le_trans := le_trans
  lt_or_le := by
    intro a b
    rcases Relation.connected (· ≤ ·) a b with lt | eq | gt
    cases lt_or_eq_of_le lt
    left; assumption; rename_i h; right; rw[h]
    right; rw [eq]
    right; assumption

instance (priority := 500) instLOofPOofLEtot [Relation.IsTotal (· ≤ (·: α))] : IsLinearOrder α := inferInstance

end IsPartialOrder

section IsLinearOrder

instance (priority := 500) [LT α] [LE α] [IsLawfulLT α] [Relation.IsPreorder (α := α) (· ≤ ·)] : IsPreOrder α where
  le_refl := Relation.refl
  le_trans := trans

instance (priority := 500) [LT α] [LE α] [IsLawfulLT α] [Relation.IsPartialOrder (α := α) (· ≤ ·) (· = ·)] : IsPartialOrder α where
  le_antisymm := antisymm (· ≤ ·)

instance (priority := 500) [LT α] [LE α] [IsLawfulLT α] [Relation.IsLinearOrder (α := α) (· ≤ ·) (· = ·)] : IsLinearOrder α := inferInstance


variable [LT α] [LE α] [IsLinearOrder α] {a b c: α}

def lt_or_le: ∀a b: α, a < b ∨ b ≤ a := IsLinearOrder.lt_or_le

instance : IsLinearOrder αᵒᵖ where
  le_antisymm := flip (le_antisymm (α := α))
  le_trans h g := le_trans (α := α) g h
  lt_or_le := by
    intro a b
    rcases lt_or_le b.get a.get with h | h
    left; assumption
    right; assumption

def le_total: ∀a b: α, a ≤ b ∨ b ≤ a := by
  intro a b
  rcases lt_or_le a b with ab | ba
  left; apply le_of_lt; assumption
  right; assumption

instance : Relation.IsTotal (α := α) (· ≤ ·) := ⟨le_total⟩
instance : Relation.IsConnected (α := α) (· < ·) := inferInstance

def le_complete: ∀a b: α, a ≤ b ∨ ¬(a ≤ b) := by
  intro a b
  rcases lt_or_le b a with ab | ba
  right
  exact (lt_iff_le_and_not_le.mp ab).right
  left; assumption
def lt_of_not_le : ¬(a ≤ b) -> b < a := by
  intro h
  cases le_total a b
  contradiction
  apply lt_of_le_of_not_le <;> assumption
def le_of_not_lt : ¬(a < b) -> b ≤ a := by
  intro h
  cases le_total b a
  assumption
  rename_i h
  apply le_of_eq; symm
  cases lt_or_eq_of_le h <;> trivial
def le_of_not_le : ¬(a ≤ b) -> b ≤ a := le_of_lt ∘ lt_of_not_le

def lt_or_gt_of_ne : a ≠ b -> a < b ∨ b < a := by
  intro h; apply Classical.byContradiction
  intro g; simp at g
  apply h; apply Relation.eq_of_not_lt_or_gt (· < ·)
  exact g.left; exact g.right

def lt_iff_not_le : a < b ↔ ¬b ≤ a := ⟨not_le_of_lt,lt_of_not_le⟩
def le_iff_not_lt : a ≤ b ↔ ¬b < a := ⟨not_lt_of_le,le_of_not_lt⟩

def not_le : ¬b ≤ a ↔ a < b := ⟨lt_of_not_le, not_le_of_lt⟩
def not_lt : ¬b < a ↔ a ≤ b := ⟨le_of_not_lt, not_lt_of_le⟩

def lt_iff_of_le_iff [LE β] [LT β] [IsLinearOrder β] {a b: α} {c d: β} : (a ≤ b ↔ c ≤ d) -> (b < a ↔ d < c) := by
  intro h
  apply Iff.trans lt_iff_not_le
  apply Iff.trans _ lt_iff_not_le.symm
  apply Iff.not_iff_not
  assumption

def le_iff_of_lt_iff [LE β] [LT β] [IsLinearOrder β] {a b: α} {c d: β} : (a < b ↔ c < d) -> (b ≤ a ↔ d ≤ c) := by
  intro h
  apply Iff.trans le_iff_not_lt
  apply Iff.trans _ le_iff_not_lt.symm
  apply Iff.not_iff_not
  assumption

def lt_trichotomy [IsLinearOrder α] (a b: α) : a < b ∨ a = b ∨ b < a := Relation.connected_by _ _ a b

end IsLinearOrder

instance Lattice.mk [LE α] [LT α] [Max α] [Min α] [IsSemiLatticeMax α] [IsSemiLatticeMin α] : IsLattice α where
  le_min := IsSemiLatticeMin.le_min

instance [LE α] [LT α] [Max α] [IsSemiLatticeMax α] : IsSemiLatticeMin αᵒᵖ where
  le_min := IsSemiLatticeMax.max_le (α := α)

instance [LE α] [LT α] [Min α] [IsSemiLatticeMin α] : IsSemiLatticeMax αᵒᵖ where
  max_le := IsSemiLatticeMin.le_min (α := α)

instance {α} [LE α] [LT α] [Max α] [Min α] [IsLattice α] : IsLattice (Opposite α) := inferInstance

section IsSemiLatticeMax

variable {α: Type*} [LE α] [LT α] [Max α] [IsSemiLatticeMax α]

def max_le: ∀{a b k: α}, a ≤ k -> b ≤ k -> a ⊔ b ≤ k :=
  IsSemiLatticeMax.max_le

def max_le_iff : ∀{a b k: α}, a ⊔ b ≤ k ↔ a ≤ k ∧ b ≤ k := by
  intro a b k
  apply Iff.intro
  intro h
  apply And.intro
  apply le_trans _ h
  apply le_max_left
  apply le_trans _ h
  apply le_max_right
  intro h
  exact max_le h.left h.right

def max_idemp: ∀a: α, a ⊔ a = a := by
  intro a
  apply le_antisymm
  apply max_le <;> rfl
  apply le_max_left

def max_comm: ∀a b: α, a ⊔ b = b ⊔ a := by
  intro a b
  apply le_antisymm
  apply max_le
  apply le_max_right
  apply le_max_left
  apply max_le
  apply le_max_right
  apply le_max_left

def max_assoc: ∀a b c: α, a ⊔ b ⊔ c = a ⊔ (b ⊔ c) := by
  intro a b c
  apply le_antisymm
  apply max_le
  apply max_le
  apply le_max_left
  apply flip le_trans
  apply le_max_right
  apply le_max_left
  apply flip le_trans
  apply le_max_right
  apply le_max_right

  apply max_le
  apply flip le_trans
  apply le_max_left
  apply le_max_left
  apply max_le
  apply flip le_trans
  apply le_max_left
  apply le_max_right
  apply le_max_right

instance : @Std.Commutative α (· ⊔ ·) := ⟨max_comm⟩
instance : @Std.Associative α (· ⊔ ·) := ⟨max_assoc⟩
instance : @Std.IdempotentOp α (· ⊔ ·) := ⟨max_idemp⟩

def of_max_eq_right {a b: α} : a ⊔ b = b -> a ≤ b := by
  intro h
  rw [←h]
  apply le_max_left
def of_max_eq_left {a b: α} : a ⊔ b = a -> b ≤ a := by
  intro h
  rw [←h]
  apply le_max_right

def max_eq_right {a b: α} : a ⊔ b = b ↔ a ≤ b := by
  apply Iff.intro
  apply of_max_eq_right
  intro h
  apply le_antisymm
  apply max_le <;> trivial
  apply le_max_right
def max_eq_left {a b: α} : a ⊔ b = a ↔ b ≤ a := by
  rw [max_comm]
  apply max_eq_right
def max_of_le (a b: α) : a ≤ b -> max a b = b := max_eq_right.mpr
def max_of_ge (a b: α) : b ≤ a -> max a b = a := max_eq_left.mpr

def lt_max_left {a b k: α} : k < a -> k < a ⊔ b := by
  simp [lt_iff_le_and_not_le]
  intro ka nak
  apply And.intro
  apply le_trans
  assumption
  apply le_max_left
  intro ak
  exact nak (max_le_iff.mp ak).left

def lt_max_right {a b k: α} : k < b -> k < a ⊔ b := by
  rw [max_comm]
  apply lt_max_left

def max_le_max {a b c d: α} :
  a ≤ c ->
  b ≤ d ->
  a ⊔ b ≤ c ⊔ d := by
  intro ac bd
  apply max_le
  apply le_trans _ (le_max_left _ _)
  assumption
  apply le_trans _ (le_max_right _ _)
  assumption

def max_self (a: α) : a ⊔ a = a := by
  apply le_antisymm
  rw [max_le_iff]; trivial
  apply le_max_left

def max_le_max_left (k a b: α) : a ≤ b -> k ⊔ a ≤ k ⊔ b := by
  intro h
  apply max_le_max
  rfl; assumption

def max_le_max_right (k a b: α) : a ≤ b -> a ⊔ k ≤ b ⊔ k := by
  intro h
  apply max_le_max
  assumption; rfl

variable [Top α] [Bot α] [IsLawfulBot α] [IsLawfulTop α]
variable {a: α}

@[simp]
def bot_max : ⊥ ⊔ a = a := by
  apply le_antisymm
  apply max_le
  apply bot_le
  rfl
  apply le_max_right

@[simp]
def max_bot : a ⊔ ⊥ = a := by
  simp [max_comm a]

@[simp]
def top_max : ⊤ ⊔ a = ⊤ := by
  apply le_antisymm
  apply max_le
  rfl
  apply le_top
  apply le_max_left

@[simp]
def max_top : a ⊔ ⊤ = ⊤ := by
  simp [max_comm a]

end IsSemiLatticeMax

section IsSemiLatticeMin

variable {α: Type*} [LE α] [LT α] [Min α] [IsSemiLatticeMin α]

def le_min: ∀{a b k: α}, k ≤ a -> k ≤ b -> k ≤ a ⊓ b :=
  IsSemiLatticeMin.le_min

@[simp]
def le_min_iff : ∀{a b k: α}, k ≤ a ⊓ b ↔ k ≤ a ∧ k ≤ b :=
  max_le_iff (α := Opposite α)

def min_idemp: ∀a: α, a ⊓ a = a :=
  max_idemp (α := Opposite α)

def min_comm: ∀a b: α, a ⊓ b = b ⊓ a :=
  max_comm (α := Opposite α)

def min_assoc: ∀a b c: α, a ⊓ b ⊓ c = a ⊓ (b ⊓ c) :=
  max_assoc (α := Opposite α)

instance : @Std.Commutative α (· ⊓ ·) := ⟨min_comm⟩
instance : @Std.Associative α (· ⊓ ·) := ⟨min_assoc⟩
instance : @Std.IdempotentOp α (· ⊓ ·) := ⟨min_idemp⟩

def of_min_eq_right {a b: α} : a ⊓ b = b -> b ≤ a :=
  of_max_eq_right (α := Opposite α)
def of_min_eq_left {a b: α} : a ⊓ b = a -> a ≤ b :=
  of_max_eq_left (α := Opposite α)

def min_eq_right {a b: α} : a ⊓ b = b ↔ b ≤ a :=
  max_eq_right (α := Opposite α)
def min_eq_left {a b: α} : a ⊓ b = a ↔ a ≤ b :=
  max_eq_left (α := Opposite α)
def min_of_le (a b: α) : a ≤ b -> min a b = a := min_eq_left.mpr
def min_of_ge (a b: α) : b ≤ a -> min a b = b := min_eq_right.mpr

def min_le_min {a b c d: α} :
  a ≤ c -> b ≤ d -> a ⊓ b ≤ c ⊓ d := max_le_max (α := αᵒᵖ)

def min_self (a: α) : a ⊓ a = a :=
  max_self (α := Opposite α) _

def min_le_min_left (k a b: α) : a ≤ b -> k ⊓ a ≤ k ⊓ b := by
  intro h
  apply min_le_min
  rfl; assumption

def min_le_min_right (k a b: α) : a ≤ b -> a ⊓ k ≤ b ⊓ k := by
  intro h
  apply min_le_min
  assumption; rfl

variable [Top α] [Bot α] [IsLawfulBot α] [IsLawfulTop α]
variable {a: α}

@[simp]
def bot_min : ⊥ ⊓ a = ⊥ :=
  top_max (α := Opposite α)

@[simp]
def min_bot : a ⊓ ⊥ = ⊥ :=
  max_top (α := Opposite α)

@[simp]
def top_min : ⊤ ⊓ a = a :=
  bot_max (α := Opposite α)

@[simp]
def min_top : a ⊓ ⊤ = a :=
  max_bot (α := Opposite α)

end IsSemiLatticeMin

section

variable [LE α] [LT α] [Min α] [Max α] [IsLattice α]

def min_le_max (a b: α) : a ⊓ b ≤ a ⊔ b :=
  le_trans (min_le_left _ _) (le_max_left _ _)

def min_max_self (a b: α) : a ⊓ (a ⊔ b) = a := by
  apply le_antisymm
  apply min_le_left
  apply le_min
  rfl; apply le_max_left

def max_min_self (a b: α) : a ⊔ (a ⊓ b) = a := by
  apply le_antisymm
  apply max_le
  rfl
  apply min_le_left
  apply le_max_left

def max_eq_iff_min_eq {a b: α} : a ⊔ b = a ↔ a ⊓ b = b := by
  rw [max_eq_left, min_eq_right]

end

section IsLinearLattice

variable [LT α] [LE α] [Min α] [Max α] [IsLinearLattice α] {a b c: α}

def clamp (x a b: α) := min (max x a) b

def min_le_iff : min a b ≤ k ↔ a ≤ k ∨ b ≤ k := by
  apply Iff.intro
  intro h
  rcases le_total a b with ab | ba
  rw [min_eq_left.mpr ab] at h
  apply Or.inl
  assumption
  rw [min_eq_right.mpr ba] at h
  apply Or.inr
  assumption
  intro h
  rcases h with ak | bk
  apply le_trans
  apply min_le_left; assumption
  apply le_trans
  apply min_le_right; assumption

def le_max_iff : k ≤ max a b ↔ k ≤ a ∨ k ≤ b := by
  apply Iff.intro
  intro h
  rcases le_total a b with ab | ba
  rw [max_eq_right.mpr ab] at h
  apply Or.inr
  assumption
  rw [max_eq_left.mpr ba] at h
  apply Or.inl
  assumption
  intro h
  rcases h with ak | bk
  apply flip le_trans
  apply le_max_left; assumption
  apply flip le_trans
  apply le_max_right; assumption

def min_lt_iff : min a b < k ↔ a < k ∨ b < k := by
  apply Iff.intro
  intro h
  rcases le_total a b with ab | ba
  rw [min_eq_left.mpr ab] at h
  apply Or.inl
  assumption
  rw [min_eq_right.mpr ba] at h
  apply Or.inr
  assumption
  intro h
  rcases h with ak | bk
  apply lt_of_le_of_lt _ ak
  apply min_le_left
  apply lt_of_le_of_lt _ bk
  apply min_le_right

def lt_min_iff : k < min a b ↔ k < a ∧ k < b := by
  apply Iff.intro
  intro h
  rcases le_total a b with ab | ba
  rw [min_eq_left.mpr ab] at h
  apply And.intro
  assumption
  apply lt_of_lt_of_le <;> assumption
  rw [min_eq_right.mpr ba] at h
  apply And.intro
  apply lt_of_lt_of_le <;> assumption
  assumption
  intro ⟨h₀,h₁⟩
  rw [←not_le, min_le_iff]
  intro h
  rcases h with h | h
  exact lt_irrefl (lt_of_lt_of_le h₀ h)
  exact lt_irrefl (lt_of_lt_of_le h₁ h)

def max_lt_iff : max a b < k ↔ a < k ∧ b < k := by
  apply Iff.intro
  intro h
  rcases le_total a b with ab | ba
  rw [max_eq_right.mpr ab] at h
  apply And.intro
  apply lt_of_le_of_lt <;> assumption
  assumption
  rw [max_eq_left.mpr ba] at h
  apply And.intro
  assumption
  apply lt_of_le_of_lt <;> assumption
  intro ⟨h₀,h₁⟩
  rw [←not_le, le_max_iff]
  intro h
  rcases h with h | h
  exact lt_irrefl (lt_of_lt_of_le h₀ h)
  exact lt_irrefl (lt_of_lt_of_le h₁ h)

def lt_max_iff : k < max a b ↔ k < a ∨ k < b := by
  apply Iff.intro
  intro h
  rcases le_total a b with ab | ba
  rw [max_eq_right.mpr ab] at h
  apply Or.inr
  assumption
  rw [max_eq_left.mpr ba] at h
  apply Or.inl
  assumption
  intro h
  rcases h with ak | bk
  apply lt_of_lt_of_le
  assumption; apply le_max_left
  apply lt_of_lt_of_le
  assumption; apply le_max_right

instance : IsLawfulMin α where
  min_le_left a b := by
    apply min_le_iff.mpr
    apply Or.inl
    rfl
  min_le_right a b := by
    apply min_le_iff.mpr
    apply Or.inr
    rfl

instance : IsLawfulMax α where
  le_max_left a b := by
    apply le_max_iff.mpr
    apply Or.inl
    rfl
  le_max_right a b := by
    apply le_max_iff.mpr
    apply Or.inr
    rfl

def clamp_eq_left (h: a ≤ b) : x ≤ a -> clamp x a b = a := by
  intro g
  unfold clamp
  rw [min_of_le, max_of_le]
  assumption
  apply max_le_iff.mpr
  apply And.intro
  apply le_trans; all_goals assumption
def clamp_eq_right (_h: a ≤ b) : b ≤ x -> clamp x a b = b := by
  intro g; unfold clamp
  rw [min_comm, min_of_le]
  apply le_trans
  assumption
  apply le_max_left
def left_le_clamp (h: a ≤ b) : a ≤ clamp x a b := by
  unfold clamp
  rcases lt_or_le a x with g | g
  rw [max_comm, max_of_le]
  apply le_min_iff.mpr
  apply And.intro
  any_goals apply le_of_lt g
  assumption
  rw [max_of_le]
  apply le_min_iff.mpr
  apply And.intro
  rfl
  assumption
  assumption
def clamp_le_right (_h: a ≤ b) : clamp x a b ≤ b := by apply min_le_right

end IsLinearLattice

section IsDecidableLinearOrder

variable [LT α] [LE α] [Min α] [Max α] [IsDecidableLinearOrder α] {a b c: α}

instance : Subsingleton (IsDecidableLinearOrder α) where
  allEq a b := by
    cases a <;> cases b
    congr <;> apply Subsingleton.allEq

instance (priority := 100) : Decidable (a ≤ b) := IsDecidableLinearOrder.decLE _ _
instance (priority := 100) : Decidable (a < b) := IsDecidableLinearOrder.decLT _ _
instance (priority := 100) : Decidable (a = b) := IsDecidableLinearOrder.decEQ _ _

def min_def [IsDecidableLinearOrder α] : ∀a b: α, min a b = if a ≤ b then a else b := by
  intro a b
  rw [IsDecidableLinearOrder.min_def]
def max_def [IsDecidableLinearOrder α] : ∀a b: α, max a b = if a ≤ b then b else a := by
  intro a b
  rw [IsDecidableLinearOrder.max_def]

instance : IsDecidableLinearOrder αᵒᵖ where
  decLE a b := inferInstanceAs (Decidable (b.get ≤ a.get))
  min_def a b := by
    apply (max_def a.get b.get).trans
    split
    split
    apply le_antisymm
    assumption
    assumption
    rfl
    split
    rfl
    rw [not_le] at *
    rename_i h g
    have := lt_asymm h g
    contradiction
  max_def a b := by
    apply (min_def a.get b.get).trans
    split
    split
    apply le_antisymm
    assumption
    assumption
    rfl
    split
    rfl
    rw [not_le] at *
    rename_i h g
    have := lt_asymm h g
    contradiction

def clamp_def (h: a ≤ b) : clamp x a b = if x < a then a else if b < x then b else x := by
  split
  rw [clamp_eq_left]
  assumption
  apply le_of_lt; assumption
  split
  rw [clamp_eq_right]
  assumption
  apply le_of_lt; assumption
  unfold clamp
  rename_i g₀ g₁
  rw [not_lt] at g₀ g₁
  rw [max_comm, max_of_le, min_of_le]
  assumption
  assumption

attribute [irreducible] clamp

end IsDecidableLinearOrder

section MinMaxOfLe

variable (α: Type*) [LE α] [LT α] [IsLinearOrder α] [DecidableLE α]

instance instSemilatticeMaxOfLe : @IsSemiLatticeMax α _ _ maxOfLe :=
  let m : Max α  := maxOfLe
  {
    max_le := by
      intro a b k ak bk
      unfold Max.max maxOfLe
      simp; split <;> assumption
    le_max_left := by
      intro a b
      unfold Max.max maxOfLe
      simp; split <;> trivial
    le_max_right := by
      intro a b
      unfold Max.max maxOfLe
      simp; split; trivial
      apply le_of_not_le
      assumption
  }

instance instSemilatticeMinOfLe : @IsSemiLatticeMin α _ _ minOfLe :=
  let m : Min α  := minOfLe
  {
    le_min := by
      intro a b k ak kb
      unfold Min.min minOfLe
      simp; split <;> assumption
    min_le_left := by
      intro a b
      unfold Min.min minOfLe
      simp; split; trivial
      apply le_of_not_le
      assumption
    min_le_right := by
      intro a b
      unfold Min.min minOfLe
      simp; split <;> trivial
  }

instance instLatticeOfLe : @IsLattice α _ _ maxOfLe minOfLe :=
  let _m : Min α  := minOfLe
  let _m : Max α  := maxOfLe
  { instSemilatticeMaxOfLe α, instSemilatticeMinOfLe α with }

end MinMaxOfLe

section Impls

instance : IsDecidableLinearOrder Bool where
  decLE := by intros; exact inferInstance
  lt_iff_le_and_not_le := by decide
  le_antisymm := by decide
  lt_or_le := by decide
  le_trans := by decide
  min_def := by decide
  max_def := by decide
  le_max_left := by decide
  le_max_right := by decide
  le_refl := by decide
  max_le := by decide
  min_le_left := by decide
  min_le_right := by decide
  le_min := by decide
instance : IsPartialOrder Bool := inferInstance
instance : IsLattice Bool := inferInstance

instance : IsLinearOrder Nat where
  lt_iff_le_and_not_le := Nat.lt_iff_le_not_le
  le_antisymm := Nat.le_antisymm
  lt_or_le := Nat.lt_or_ge
  le_trans := Nat.le_trans
instance : IsDecidableLinearOrder Nat := {
  inferInstanceAs (IsPartialOrder Nat),
  inferInstanceAs (IsLinearOrder Nat),
  instLatticeOfLe Nat with
}
instance : IsPartialOrder Nat := inferInstance
instance : IsLattice Nat := inferInstance

instance : IsLinearOrder (Fin n) where
  lt_iff_le_and_not_le := Nat.lt_iff_le_not_le
  le_antisymm := by
    intro a b ab ba
    apply Fin.val_inj.mp
    apply le_antisymm <;> assumption
  lt_or_le _ _ := Nat.lt_or_ge _ _
  le_trans := Nat.le_trans
instance : Min (Fin n) := minOfLe
instance : Max (Fin n) := maxOfLe
instance : IsDecidableLinearOrder (Fin n) := {
  inferInstanceAs (IsLinearOrder (Fin n)),
  instLatticeOfLe (Fin n) with
}
instance : IsPartialOrder (Fin n) := inferInstance
instance : IsLattice (Fin n) := inferInstance

@[simp]
def Fin.min_val (a b: Fin n) : (min a b).val = min a.val b.val := by
  show Fin.val (if _ then _ else _) = (if _ then _ else _)
  split
  rw [if_pos]
  assumption
  rw [if_neg]
  assumption
@[simp]
def Fin.max_val (a b: Fin n) : (max a b).val = max a.val b.val := by
  show Fin.val (if _ then _ else _) = (if _ then _ else _)
  split
  rw [if_pos]
  assumption
  rw [if_neg]
  assumption

instance : Bot Bool where
  bot := false
instance : IsLawfulBot Bool where
  bot_le := Bool.false_le

instance : Bot Nat where
  bot := 0
instance : IsLawfulBot Nat where
  bot_le := Nat.zero_le

instance : IsLinearOrder Int where
  lt_iff_le_and_not_le := Int.lt_iff_le_not_le
  le_antisymm := Int.le_antisymm
  le_trans := Int.le_trans
  lt_or_le a b := by
    rcases Int.decEq a b with a_ne_b | a_eq_b
    rcases Int.lt_or_gt_of_ne a_ne_b with ab | ba
    left; assumption
    right; apply Int.le_of_lt; assumption
    right; subst b; apply Int.le_refl
instance : IsDecidableLinearOrder Int := {
  inferInstanceAs (IsPartialOrder Int),
  inferInstanceAs (IsLinearOrder Int),
  instLatticeOfLe Int with
}
instance : IsPartialOrder Int := inferInstance
instance : IsLattice Int := inferInstance

def le_setoid (α: Type*) [LE α] [LT α] [IsPreOrder α] : Setoid α where
  r a b := a ≤ b ∧ b ≤ a
  iseqv := {
    refl _ := ⟨le_refl _, le_refl _⟩
    symm h := ⟨h.2, h.1⟩
    trans h g := ⟨le_trans h.1 g.1, le_trans g.2 h.2⟩
  }

namespace Classical

variable [LE α] [LT α] [Min α] [Max α] [IsLinearLattice α]

noncomputable scoped instance (priority := 10) : IsDecidableLinearOrder α where
  min_def := by
    intro a b
    split <;> rename_i h
    rwa [min_eq_left.mpr]
    rw [not_le] at h
    rw [min_eq_right.mpr]
    apply le_of_lt; assumption
  max_def := by
    intro a b
    split <;> rename_i h
    rwa [max_eq_right.mpr]
    rw [not_le] at h
    rw [max_eq_left.mpr]
    apply le_of_lt; assumption

end Classical

end Impls

section Pi

variable {ι: Type*} {α: ι -> Type*} [∀x, LE (α x)] [∀x, LT (α x)]
  [∀x, Max (α x)] [∀x, Min (α x)]

instance : LE (∀x, α x) where
  le f g := ∀x, f x ≤ g x

instance : LT (∀x, α x) where
  lt f g := f ≤ g ∧ ¬g ≤ f

instance : IsLawfulLT (∀x, α x) where
  lt_iff_le_and_not_le := Iff.rfl

instance [∀x, IsPreOrder (α x)] : IsPreOrder (∀x, α x) where
  le_refl _ _ := le_refl _
  le_trans h g _ := le_trans (h _) (g _)

instance [∀x, IsPartialOrder (α x)] : IsPartialOrder (∀x, α x) where
  le_antisymm := by
    intro a b ha hb
    ext x
    apply le_antisymm
    apply ha
    apply hb

instance : Max (∀x, α x) where
  max f g x := max (f x) (g x)

instance : Min (∀x, α x) where
  min f g x := min (f x) (g x)

instance [∀x, IsSemiLatticeMax (α x)] : IsSemiLatticeMax (∀x, α x) where
  le_max_left := by
    intro f g i
    apply le_max_left
  le_max_right := by
    intro f g i
    apply le_max_right
  max_le := by
    intro f g k fk gk  i
    apply max_le
    apply fk
    apply gk

instance [∀x, IsSemiLatticeMin (α x)] : IsSemiLatticeMin (∀x, α x) where
  min_le_left := by
    intro f g i
    apply min_le_left
  min_le_right := by
    intro f g i
    apply min_le_right
  le_min := by
    intro f g k kf kg i
    apply le_min
    apply kf
    apply kg

instance [∀x, IsLattice (α x)] : IsLattice (∀x, α x) := inferInstance

end Pi

namespace Subtype

variable {P: α -> Prop} [LE α] [LT α]

instance : LT (Subtype P) where
  lt a b := a.val < b.val
instance : LE (Subtype P) where
  le a b := a.val ≤ b.val

instance [IsLawfulLT α] : IsLawfulLT (Subtype P) where
  lt_iff_le_and_not_le := lt_iff_le_and_not_le (α := α)

instance [IsPreOrder α] : IsPreOrder (Subtype P) where
  le_refl _ := le_refl (α := α) _
  le_trans := le_trans (α := α)

instance [IsPartialOrder α] : IsPartialOrder (Subtype P) where
  le_antisymm := by
    intro a b ha hb
    cases a; cases b; congr
    apply le_antisymm
    assumption
    assumption

local instance [IsLinearOrder α] : Relation.IsTotal ((· ≤ ·): Subtype P -> Subtype P -> Prop) where
  total a b := by apply le_total (α := α)

instance [IsLinearOrder α] : IsLinearOrder (Subtype P) := inferInstance

end Subtype
