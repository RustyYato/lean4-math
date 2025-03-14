import Math.Order.Partial

class IsLinearOrder (α: Type*) [LT α] [LE α] : Prop extends IsLawfulLT α where
  le_antisymm: ∀{a b: α}, a ≤ b -> b ≤ a -> a = b
  lt_or_le: ∀a b: α, a < b ∨ b ≤ a
  le_trans: ∀{a b c: α}, a ≤ b -> b ≤ c -> a ≤ c

-- do not use this in bounds directly, this is only meant to be used to create a PreOrder
-- for example, via `GaloisConnection`
class LinearOrder (α: Type*) extends LT α, LE α, IsLinearOrder α

instance [LT α] [LE α] [IsLinearOrder α] : IsPartialOrder α where
  le_antisymm := IsLinearOrder.le_antisymm
  le_refl := by
    intro a
    rcases IsLinearOrder.lt_or_le a a with r | r
    exact (lt_iff_le_and_not_le.mp r).left
    assumption
  le_trans := IsLinearOrder.le_trans

class IsLinearMinMaxOrder (α: Type*) [LT α] [LE α] [Min α] [Max α] : Prop extends IsLinearOrder α where
  min_iff_le_left: ∀{a b: α}, a ≤ b ↔ min a b = a := by
    intro a b
    apply Iff.intro
    intro h
    suffices (if a ≤ b then a else b) = a from this
    rw [if_pos h]
    intro h
    have h : (if a ≤ b then a else b) = a := h
    split at h
    assumption
    subst h
    apply le_refl
  min_iff_le_right: ∀{a b: α}, b ≤ a ↔ min a b = b := by
    intro a b
    apply Iff.intro
    intro h
    suffices (if a ≤ b then a else b) = b from this
    split
    apply le_antisymm <;> assumption
    rfl
    intro h
    have h : (if a ≤ b then a else b) = b := h
    split at h
    subst h
    apply le_refl
    apply le_of_lt
    apply lt_of_not_le
    assumption
  max_iff_le_left: ∀{a b: α}, a ≤ b ↔ max a b = b := by
    intro a b
    apply Iff.intro
    intro h
    suffices (if a ≤ b then b else a) = b from this
    rw [if_pos]
    assumption
    intro h
    have h : (if a ≤ b then b else a) = b := h
    split at h
    assumption
    subst h
    apply le_refl
  max_iff_le_right: ∀{a b: α}, b ≤ a ↔ max a b = a := by
    intro a b
    apply Iff.intro
    intro h
    suffices (if a ≤ b then b else a) = a from this
    split
    apply le_antisymm <;> assumption
    rfl
    intro h
    have h : (if a ≤ b then b else a) = a := h
    split at h
    subst h
    apply le_refl
    apply le_of_lt
    apply lt_of_not_le
    assumption

-- do not use this in bounds directly, this is only meant to be used to create a PreOrder
-- for example, via `GaloisConnection`
class LinearMinMaxOrder (α: Type*) extends LT α, LE α, Min α, Max α, IsLinearMinMaxOrder α

variable {α: Type*} {a b c d: α}
variable [LT α] [LE α] [Min α] [Max α]

def clamp (x a b: α) := min (max x a) b

section

variable [IsLinearOrder α]

def lt_or_le: ∀a b: α, a < b ∨ b ≤ a := IsLinearOrder.lt_or_le

def le_total: ∀a b: α, a ≤ b ∨ b ≤ a := by
  intro a b
  rcases lt_or_le a b with ab | ba
  left; apply le_of_lt; assumption
  right; assumption
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
  intro h
  cases le_total a b <;> rename_i h
  cases lt_or_eq_of_le h
  apply Or.inl
  assumption
  contradiction
  apply Or.inr
  apply lt_of_le_of_ne
  assumption
  symm
  assumption

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

def compare_linear (a b: α) : a < b ∨ a = b ∨ b < a := by
  cases lt_or_le a b
  left; assumption
  right
  rename_i h
  cases lt_or_eq_of_le h
  right; assumption
  left; symm; assumption

instance : @Relation.IsTrichotomous α (· < ·) where
  tri a b := by
    rcases lt_or_le a b with ab | ba
    left; assumption
    right
    rcases lt_or_eq_of_le ba
    right; assumption
    left; symm; assumption

instance : @Relation.IsTotal α (· ≤ ·) where
  total a b := by
    rcases lt_or_le a b with ab | ba
    left; apply le_of_lt; assumption
    right; assumption

def lt_trichotomy [IsLinearOrder α] := (inferInstanceAs (@Relation.IsTrichotomous α (· < ·))).tri

end

instance instLOofPOofLTtri [IsPartialOrder α] [Relation.IsTrichotomous (· < (·: α))] : IsLinearOrder α where
  lt_iff_le_and_not_le := lt_iff_le_and_not_le
  le_antisymm := le_antisymm
  le_trans := le_trans
  lt_or_le := by
    intro a b
    rcases Relation.trichotomous (· < ·) a b with lt | eq | gt
    left; assumption
    right; rw [eq]
    right; apply le_of_lt; assumption

instance instLOofPOofLEtri [IsPartialOrder α] [Relation.IsTrichotomous (· ≤ (·: α))] : IsLinearOrder α where
  lt_iff_le_and_not_le := lt_iff_le_and_not_le
  le_antisymm := le_antisymm
  le_trans := le_trans
  lt_or_le := by
    intro a b
    rcases Relation.trichotomous (· ≤ ·) a b with lt | eq | gt
    cases lt_or_eq_of_le lt
    left; assumption; rename_i h; right; rw[h]
    right; rw [eq]
    right; assumption

variable [IsLinearMinMaxOrder α]

def min_iff_le_left: a ≤ b ↔ min a b = a := IsLinearMinMaxOrder.min_iff_le_left
def min_iff_le_right: b ≤ a ↔ min a b = b := IsLinearMinMaxOrder.min_iff_le_right
def max_iff_le_left: a ≤ b ↔ max a b = b := IsLinearMinMaxOrder.max_iff_le_left
def max_iff_le_right: b ≤ a ↔ max a b = a := IsLinearMinMaxOrder.max_iff_le_right

def min_le_iff : min a b ≤ k ↔ a ≤ k ∨ b ≤ k := by
  apply Iff.intro
  intro h
  rcases le_total a b with ab | ba
  rw [min_iff_le_left.mp ab] at h
  apply Or.inl
  assumption
  rw [min_iff_le_right.mp ba] at h
  apply Or.inr
  assumption
  intro h
  rcases h with ak | bk <;> rcases le_total a b with ab | ba
  any_goals try rw [min_iff_le_left.mp ab]
  any_goals try rw [min_iff_le_right.mp ba]
  any_goals assumption
  apply le_trans <;> assumption
  apply le_trans <;> assumption

def le_min_iff : k ≤ min a b ↔ k ≤ a ∧ k ≤ b := by
  apply Iff.intro
  intro h
  rcases le_total a b with ab | ba
  rw [min_iff_le_left.mp ab] at h
  apply And.intro
  assumption
  apply le_trans <;> assumption
  rw [min_iff_le_right.mp ba] at h
  apply And.intro
  apply le_trans <;> assumption
  assumption
  intro ⟨h₀,h₁⟩
  rcases le_total a b with ab | ba
  rw [min_iff_le_left.mp ab]
  assumption
  rw [min_iff_le_right.mp ba]
  assumption

def max_le_iff : max a b ≤ k ↔ a ≤ k ∧ b ≤ k := by
  apply Iff.intro
  intro h
  rcases le_total a b with ab | ba
  rw [max_iff_le_left.mp ab] at h
  apply And.intro
  apply le_trans <;> assumption
  assumption
  rw [max_iff_le_right.mp ba] at h
  apply And.intro
  assumption
  apply le_trans <;> assumption
  intro ⟨h₀,h₁⟩
  rcases le_total a b with ab | ba
  rw [max_iff_le_left.mp ab]
  assumption
  rw [max_iff_le_right.mp ba]
  assumption

def le_max_iff : k ≤ max a b ↔ k ≤ a ∨ k ≤ b := by
  apply Iff.intro
  intro h
  rcases le_total a b with ab | ba
  rw [max_iff_le_left.mp ab] at h
  apply Or.inr
  assumption
  rw [max_iff_le_right.mp ba] at h
  apply Or.inl
  assumption
  intro h
  rcases h with ak | bk <;> rcases le_total a b with ab | ba
  any_goals try rw [max_iff_le_left.mp ab]
  any_goals try rw [max_iff_le_right.mp ba]
  any_goals assumption
  apply le_trans <;> assumption
  apply le_trans <;> assumption

def min_lt_iff : min a b < k ↔ a < k ∨ b < k := by
  apply Iff.intro
  intro h
  rcases le_total a b with ab | ba
  rw [min_iff_le_left.mp ab] at h
  apply Or.inl
  assumption
  rw [min_iff_le_right.mp ba] at h
  apply Or.inr
  assumption
  intro h
  rcases h with ak | bk <;> rcases le_total a b with ab | ba
  any_goals try rw [min_iff_le_left.mp ab]
  any_goals try rw [min_iff_le_right.mp ba]
  any_goals assumption
  apply lt_of_le_of_lt <;> assumption
  apply lt_of_le_of_lt <;> assumption

def lt_min_iff : k < min a b ↔ k < a ∧ k < b := by
  apply Iff.intro
  intro h
  rcases le_total a b with ab | ba
  rw [min_iff_le_left.mp ab] at h
  apply And.intro
  assumption
  apply lt_of_lt_of_le <;> assumption
  rw [min_iff_le_right.mp ba] at h
  apply And.intro
  apply lt_of_lt_of_le <;> assumption
  assumption
  intro ⟨h₀,h₁⟩
  rcases le_total a b with ab | ba
  rw [min_iff_le_left.mp ab]
  assumption
  rw [min_iff_le_right.mp ba]
  assumption

def max_lt_iff : max a b < k ↔ a < k ∧ b < k := by
  apply Iff.intro
  intro h
  rcases le_total a b with ab | ba
  rw [max_iff_le_left.mp ab] at h
  apply And.intro
  apply lt_of_le_of_lt <;> assumption
  assumption
  rw [max_iff_le_right.mp ba] at h
  apply And.intro
  assumption
  apply lt_of_le_of_lt <;> assumption
  intro ⟨h₀,h₁⟩
  rcases le_total a b with ab | ba
  rw [max_iff_le_left.mp ab]
  assumption
  rw [max_iff_le_right.mp ba]
  assumption

def lt_max_iff : k < max a b ↔ k < a ∨ k < b := by
  apply Iff.intro
  intro h
  rcases le_total a b with ab | ba
  rw [max_iff_le_left.mp ab] at h
  apply Or.inr
  assumption
  rw [max_iff_le_right.mp ba] at h
  apply Or.inl
  assumption
  intro h
  rcases h with ak | bk <;> rcases le_total a b with ab | ba
  any_goals try rw [max_iff_le_left.mp ab]
  any_goals try rw [max_iff_le_right.mp ba]
  any_goals assumption
  apply lt_of_lt_of_le <;> assumption
  apply lt_of_lt_of_le <;> assumption

def min_le_max (a b: α) : min a b ≤ max a b := by
  rcases le_total a b with ab | ba
  rw [min_iff_le_left.mp ab, max_iff_le_left.mp ab]
  assumption
  rw [min_iff_le_right.mp ba, max_iff_le_right.mp ba]
  assumption

def min_le_left (a b: α) : min a b ≤ a := by
  apply min_le_iff.mpr
  apply Or.inl
  rfl

def min_le_right (a b: α) : min a b ≤ b := by
  apply min_le_iff.mpr
  apply Or.inr
  rfl

def le_max_left (a b: α) : a ≤ max a b := by
  apply le_max_iff.mpr
  apply Or.inl
  rfl

def le_max_right (a b: α) : b ≤ max a b := by
  apply le_max_iff.mpr
  apply Or.inr
  rfl

def max_le : a ≤ k -> b ≤ k -> max a b ≤ k := by
  intro h g
  apply max_le_iff.mpr
  apply And.intro <;> assumption

def le_min : k ≤ a -> k ≤ b -> k ≤ min a b := by
  intro h g
  apply le_min_iff.mpr
  apply And.intro <;> assumption

def min_of_le (a b: α) : a ≤ b -> min a b = a := min_iff_le_left.mp
def max_of_le (a b: α) : a ≤ b -> max a b = b := max_iff_le_left.mp

def min_le_comm (a b: α) : min a b ≤ min b a := by
  apply le_min_iff.mpr
  apply And.intro
  apply min_le_right
  apply min_le_left

def min_comm (a b: α) : min a b = min b a := by
  apply le_antisymm
  apply min_le_comm
  apply min_le_comm

def max_le_comm (a b: α) : max a b ≤ max b a := by
  apply max_le_iff.mpr
  apply And.intro
  apply le_max_right
  apply le_max_left

def max_comm (a b: α) : max a b = max b a := by
  apply le_antisymm
  apply max_le_comm
  apply max_le_comm

def min_assoc (a b c: α) : min a (min b c) = min (min a b) c := by
  apply le_antisymm
  · repeat any_goals apply le_min_iff.mpr; apply And.intro
    apply min_le_left
    apply min_le_iff.mpr
    apply Or.inr
    apply min_le_left
    apply min_le_iff.mpr
    apply Or.inr
    apply min_le_right
  · repeat any_goals apply le_min_iff.mpr; apply And.intro
    apply min_le_iff.mpr
    apply Or.inl
    apply min_le_left
    apply min_le_iff.mpr
    apply Or.inl
    apply min_le_right
    apply min_le_right

def max_assoc (a b c: α) : max a (max b c) = max (max a b) c := by
  apply le_antisymm
  · repeat any_goals apply max_le_iff.mpr; apply And.intro
    apply le_max_iff.mpr
    apply Or.inl
    apply le_max_left
    apply le_max_iff.mpr
    apply Or.inl
    apply le_max_right
    apply le_max_right
  · repeat any_goals apply max_le_iff.mpr; apply And.intro
    apply le_max_left
    apply le_max_iff.mpr
    apply Or.inr
    apply le_max_left
    apply le_max_iff.mpr
    apply Or.inr
    apply le_max_right

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

attribute [irreducible] clamp

class IsDecidableLinearOrder (α: Type _) [LE α] [LT α] [Min α] [Max α] extends IsLinearMinMaxOrder α where
  decLE (a b: α): Decidable (a ≤ b) := by intros; exact inferInstance
  decLT (a b: α): Decidable (a < b) := decidable_of_iff _ (lt_iff_le_and_not_le (a := a) (b := b)).symm
  decEQ (a b: α): Decidable (a = b) := decidable_of_iff (a ≤ b ∧ b ≤ a) (by
  apply Iff.intro
  · rintro ⟨ab,ba⟩
    apply le_antisymm ab ba
  · intro h
    subst h
    apply And.intro <;> rfl)
  min_def (a b: α): min a b = if a ≤ b then a else b := by intros; rfl
  max_def (a b: α): max a b = if a ≤ b then b else a := by intros; rfl

-- do not use this in bounds directly, this is only meant to be used to create a PreOrder
-- for example, via `GaloisConnection`
class DecidableLinearOrder (α: Type*) extends LT α, LE α, Min α, Max α, IsDecidableLinearOrder α

instance : Subsingleton (IsDecidableLinearOrder α) where
  allEq a b := by
    cases a <;> cases b
    congr <;> apply Subsingleton.allEq

instance (priority := 100) [IsDecidableLinearOrder α] : Decidable (a ≤ b) := IsDecidableLinearOrder.decLE _ _
instance (priority := 100) [IsDecidableLinearOrder α] : Decidable (a < b) := IsDecidableLinearOrder.decLT _ _
instance (priority := 100) [IsDecidableLinearOrder α] : Decidable (a = b) := IsDecidableLinearOrder.decEQ _ _

variable [IsDecidableLinearOrder α]

def min_def [IsDecidableLinearOrder α] : ∀a b: α, min a b = if a ≤ b then a else b := by
  intro a b
  rw [IsDecidableLinearOrder.min_def]
def max_def [IsDecidableLinearOrder α] : ∀a b: α, max a b = if a ≤ b then b else a := by
  intro a b
  rw [IsDecidableLinearOrder.max_def]

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

instance : IsDecidableLinearOrder Bool where
  decLE := by intros; exact inferInstance
  lt_iff_le_and_not_le := by decide
  le_antisymm := by decide
  lt_or_le := by decide
  le_trans := by decide
  min_def := by decide
  max_def := by decide
  min_iff_le_left := by decide
  min_iff_le_right := by decide
  max_iff_le_left := by decide
  max_iff_le_right := by decide

instance : IsLinearOrder Nat where
  lt_iff_le_and_not_le := Nat.lt_iff_le_not_le
  le_antisymm := Nat.le_antisymm
  lt_or_le := Nat.lt_or_ge
  le_trans := Nat.le_trans
instance : IsDecidableLinearOrder Nat where

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
instance : IsDecidableLinearOrder (Fin n) where

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
instance : IsDecidableLinearOrder Int where

variable {β γ: Type*} {x y z: β} {f: α -> β} {g: β -> γ }
variable [LT β] [LE β]
variable [LT γ] [LE γ]

namespace StrictMonotoneOn

def InjectiveOn [IsPreOrder β] (m: StrictMonotoneOn f s) : Function.InjectiveOn f s := by
  intro x y hx hy hxy
  rcases lt_trichotomy x y with h | h | h
  have := m hx hy h
  rw [hxy] at this
  have := lt_irrefl this
  contradiction
  assumption
  have := m hy hx h
  rw [hxy] at this
  have := lt_irrefl this
  contradiction

end StrictMonotoneOn

namespace StrictMonotone

def Injective [IsPreOrder β] (m: StrictMonotone f) : Function.Injective f := by
  rw [←StrictMonotone.iffOnUniv] at m
  rw [←Function.InjectiveOn_univ_iff_Injective]
  apply StrictMonotoneOn.InjectiveOn
  assumption

end StrictMonotone
