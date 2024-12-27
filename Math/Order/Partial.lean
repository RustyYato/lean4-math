import Math.Type.Notation
import Math.Logic.Basic
import Math.Order.Dual

class IsPartialOrder (α: Type*) [LT α] [LE α]: Prop where
  lt_iff_le_and_not_le: ∀{a b: α}, a < b ↔ a ≤ b ∧ ¬b ≤ a
  le_antisymm: ∀{a b: α}, a ≤ b -> b ≤ a -> a = b
  le_refl: ∀a: α, a ≤ a
  le_trans: ∀{a b c: α}, a ≤ b -> b ≤ c -> a ≤ c

variable {α: Type*} {a b c d: α}
variable [LT α] [LE α] [IsPartialOrder α]

@[refl, simp]
def le_refl: ∀a: α, a ≤ a := IsPartialOrder.le_refl
def lt_iff_le_and_not_le: a < b ↔ a ≤ b ∧ ¬b ≤ a := IsPartialOrder.lt_iff_le_and_not_le
def le_antisymm: a ≤ b -> b ≤ a -> a = b := IsPartialOrder.le_antisymm
def le_trans: a ≤ b -> b ≤ c -> a ≤ c := IsPartialOrder.le_trans

def le_of_lt: a < b -> a ≤ b := fun h => (lt_iff_le_and_not_le.mp h).left
def lt_of_le_of_not_le : a ≤ b -> ¬(b ≤ a) -> a < b := (lt_iff_le_and_not_le.mpr ⟨·, ·⟩)

def le_of_eq: a = b -> a ≤ b := fun h => h ▸ le_refl _
def not_le_of_lt (hab : a < b) : ¬ b ≤ a := (lt_iff_le_and_not_le.1 hab).2
def not_lt_of_le (hab : a ≤ b) : ¬ b < a := imp_not_comm.1 not_le_of_lt hab
def lt_irrefl: ¬a < a := fun h => (lt_iff_le_and_not_le.mp h).right (le_refl _)
def ne_of_lt: a < b -> a ≠ b := fun h g => lt_irrefl (g ▸ h)
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
def le_of_lt_or_eq: a < b ∨ a = b -> a ≤ b := by
  intro h
  cases h
  apply le_of_lt; assumption
  apply le_of_eq; assumption
def lt_of_le_of_ne: a ≤ b -> a ≠ b -> a < b := by
  intro h g
  cases lt_or_eq_of_le h
  assumption
  contradiction
def lt_trans : a < b -> b < c -> a < c := by
  intro ab bc
  apply lt_of_le_of_ne
  apply le_trans <;> (apply le_of_lt; assumption)
  intro h
  subst c
  have ⟨_,nba⟩ := lt_iff_le_and_not_le.mp ab
  have ⟨ba,_⟩ := lt_iff_le_and_not_le.mp bc
  contradiction
def lt_of_lt_of_le : a < b -> b ≤ c -> a < c := by
  intro ab bc
  cases lt_or_eq_of_le bc <;> rename_i bc
  apply lt_trans <;> assumption
  subst c
  assumption
def lt_of_le_of_lt : a ≤ b -> b < c -> a < c := by
  intro ab bc
  cases lt_or_eq_of_le ab <;> rename_i ab
  apply lt_trans <;> assumption
  subst a
  assumption

def lt_asymm : a < b -> b < a -> False := (lt_irrefl <| lt_trans · ·)

instance [IsPartialOrder α] : IsPartialOrder (OrderDual α) where
  lt_iff_le_and_not_le := by
    intro a b
    apply Iff.trans (lt_iff_le_and_not_le (α := α))
    rfl
  le_antisymm := by
    intro a b ab ba
    apply le_antisymm (α := α) <;> assumption
  le_refl := le_refl (α := α)
  le_trans := flip (le_trans (α := α))
