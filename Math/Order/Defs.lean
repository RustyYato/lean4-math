import Math.Logic.Basic
import Math.Order.Notation
import Math.Relation.Basic
import Math.Data.Opposite

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

class IsDecidableLinearOrder (α: Type _) [LE α] [LT α] [Min α] [Max α] extends IsLinearMinMaxOrder α where
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
def lt_trans : a < b -> b < c -> a < c := by
  intro ab bc
  replace ⟨ab, nba⟩ := lt_iff_le_and_not_le.mp ab
  replace ⟨bc, ncb⟩ := lt_iff_le_and_not_le.mp bc
  apply lt_iff_le_and_not_le.mpr ⟨le_trans ab bc, _⟩
  intro h
  apply nba
  apply le_trans
  assumption
  assumption
def lt_of_lt_of_le : a < b -> b ≤ c -> a < c := by
  intro ab bc
  replace ⟨ab, nba⟩ := lt_iff_le_and_not_le.mp ab
  apply lt_iff_le_and_not_le.mpr ⟨le_trans ab bc, _⟩
  intro h
  apply nba
  apply le_trans
  assumption
  assumption
def lt_of_le_of_lt : a ≤ b -> b < c -> a < c := by
  intro ab bc
  replace ⟨bc, ncb⟩ := lt_iff_le_and_not_le.mp bc
  apply lt_iff_le_and_not_le.mpr ⟨le_trans ab bc, _⟩
  intro h
  apply ncb
  apply le_trans
  assumption
  assumption

def lt_asymm : a < b -> b < a -> False := (lt_irrefl <| lt_trans · ·)

instance : @Relation.IsTrans α (· < ·) where
  trans := lt_trans
instance : @Relation.IsTrans α (· ≤ ·) where
  trans := le_trans
instance : @Relation.IsIrrefl α (· < ·) where
  irrefl := lt_irrefl
instance : @Relation.IsRefl α (· ≤ ·) where
  refl := le_refl

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

def lt_or_eq_of_le: a ≤ b -> a < b ∨ a = b := by
  intro h
  by_cases g:b ≤ a
  right
  apply le_antisymm
  assumption
  assumption
  left
  apply lt_iff_le_and_not_le.mpr
  apply And.intro <;> assumption
def lt_of_le_of_ne: a ≤ b -> a ≠ b -> a < b := by
  intro h g
  cases lt_or_eq_of_le h
  assumption
  contradiction
def le_iff_lt_or_eq: a ≤ b ↔ a < b ∨ a = b := Iff.intro lt_or_eq_of_le le_of_lt_or_eq

instance : @Relation.IsAntisymm α (· ≤ ·) where
  antisymm := le_antisymm

instance [IsPartialOrder α] : IsPartialOrder αᵒᵖ where
  le_antisymm := by
    intro a b ab ba
    apply le_antisymm (α := α) <;> assumption

instance (priority := 500) instLOofPOofLTtri [Relation.IsTrichotomous (· < (·: α))] : IsLinearOrder α where
  lt_iff_le_and_not_le := lt_iff_le_and_not_le
  le_antisymm := le_antisymm
  le_trans := le_trans
  lt_or_le := by
    intro a b
    rcases Relation.trichotomous (· < ·) a b with lt | eq | gt
    left; assumption
    right; rw [eq]
    right; apply le_of_lt; assumption

instance (priority := 500) instLOofPOofLEtri [Relation.IsTrichotomous (· ≤ (·: α))] : IsLinearOrder α where
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

instance (priority := 500) instLOofPOofLEtot [Relation.IsTotal (· ≤ (·: α))] : IsLinearOrder α := inferInstance

end IsPartialOrder

section IsLinearOrder

variable [LT α] [LE α] [IsLinearOrder α] {a b c: α}

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

end IsLinearOrder

section IsLinearMinMaxOrder

variable [LT α] [LE α] [Min α] [Max α] [IsLinearMinMaxOrder α] {a b c: α}

def clamp (x a b: α) := min (max x a) b

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

end IsLinearMinMaxOrder

section

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

end

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
instance : IsPartialOrder Bool := inferInstance

instance : IsLinearOrder Nat where
  lt_iff_le_and_not_le := Nat.lt_iff_le_not_le
  le_antisymm := Nat.le_antisymm
  lt_or_le := Nat.lt_or_ge
  le_trans := Nat.le_trans
instance : IsDecidableLinearOrder Nat where
instance : IsPartialOrder Nat := inferInstance

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
instance : IsPartialOrder (Fin n) := inferInstance

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
instance : IsPartialOrder Int := inferInstance

def le_setoid (α: Type*) [LE α] [LT α] [IsPreOrder α] : Setoid α where
  r a b := a ≤ b ∧ b ≤ a
  iseqv := {
    refl _ := ⟨le_refl _, le_refl _⟩
    symm h := ⟨h.2, h.1⟩
    trans h g := ⟨le_trans h.1 g.1, le_trans g.2 h.2⟩
  }
