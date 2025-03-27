import Math.Algebra.Field.Basic
import Math.Algebra.Semiring.Order.Defs
import Math.Ops.CheckedOrder

section

variable [SemifieldOps α] [IsNonCommSemifield α] [LE α] [LT α] [IsOrderedSemiring α]

def mul_lt_mul_of_pos_left: ∀(a b : α), a < b → ∀ (c : α), 0 < c → c * a < c * b := by
  intro a b ab c cpos
  apply lt_of_le_of_ne
  apply mul_le_mul_of_nonneg_left
  apply le_of_lt
  assumption
  apply le_of_lt
  assumption
  intro h
  have : c ≠ 0 := by symm; apply ne_of_lt; assumption
  have : c⁻¹? * (c * a) = c⁻¹? * (c * b) := by rw [h]
  rw [←mul_assoc, ←mul_assoc, inv?_mul_cancel, one_mul, one_mul] at this
  subst b
  exact lt_irrefl ab

def mul_lt_mul_of_pos_right: ∀(a b : α), a < b → ∀ (c : α), 0 < c → a * c < b * c := by
  intro a b ab c cpos
  apply lt_of_le_of_ne
  apply mul_le_mul_of_nonneg_right
  apply le_of_lt
  assumption
  apply le_of_lt
  assumption
  intro h
  have : c ≠ 0 := by symm; apply ne_of_lt; assumption
  have : (a * c) * c⁻¹? = (b * c) * c⁻¹? := by rw [h]
  rw [mul_assoc, mul_assoc, mul_inv?_cancel, mul_one, mul_one] at this
  subst b
  exact lt_irrefl ab

variable [IsLinearOrder α]

def inv?_pos (a: α) (h: 0 < a): 0 < a⁻¹? := by
  have anz : a ≠ 0 := by
    intro g; rw [g] at h
    exact lt_irrefl h
  apply lt_of_not_le
  intro g; replace g := lt_or_eq_of_le g
  cases g <;> rename_i g
  · have := mul_lt_mul_of_pos_left _ _ g _ h
    rw [mul_inv?_cancel, mul_zero] at this
    exact lt_irrefl (lt_trans this zero_lt_one)
  · have := mul_inv?_cancel a anz
    rw [g, mul_zero] at this
    exact zero_ne_one _ this

def inv?_lt_inv? [IsCommMagma α] (a b: α) (ha: 0 < a) (hb: 0 < b) : a⁻¹? < b⁻¹? ↔ b < a := by
  revert a b
  suffices ∀(a b: α) (ha: 0 < a) (hb: 0 < b), a < b -> b⁻¹? < a⁻¹? by
    intro a b ha hb
    apply flip Iff.intro
    apply this
    assumption
    assumption
    intro h
    have := this _ _ ?_ ?_ h
    rw [inv?_inv?, inv?_inv?] at this
    assumption
    apply inv?_pos
    assumption
    apply inv?_pos
    assumption
  intro a b ha hb h
  have := mul_lt_mul_of_pos_left _ _ h (a⁻¹? * b⁻¹?) ?_
  rw [mul_assoc _ _ b, mul_comm (a⁻¹?), mul_assoc, inv?_mul_cancel,
    inv?_mul_cancel, mul_one, mul_one] at this
  assumption
  rw (occs := [1]) [←zero_mul (b⁻¹?)]
  apply mul_lt_mul_of_pos_right
  apply inv?_pos; assumption
  apply inv?_pos; assumption

def lt_iff_mul_lt_mul_of_pos_right (a b k: α) (h: 0 < k) : a < b ↔ a * k < b * k := by
  revert a b k
  suffices ∀(a b k : α), 0 < k → a < b -> a * k < b * k by
    intro a b k kpos
    apply Iff.intro
    apply this
    assumption
    intro h
    have := this _ _ k⁻¹? (inv?_pos _ kpos) h
    rw [mul_assoc, mul_assoc, mul_inv?_cancel, mul_one, mul_one] at this
    assumption
  intro a b k kpos altb
  apply mul_lt_mul_of_pos_right
  assumption
  assumption

def lt_iff_mul_lt_mul_of_pos_left (a b k: α) (h: 0 < k) : a < b ↔ k * a < k * b := by
  revert a b k
  suffices ∀(a b k : α), 0 < k → a < b -> k * a < k * b by
    intro a b k kpos
    apply Iff.intro
    apply this
    assumption
    intro h
    have := this _ _ k⁻¹? (inv?_pos _ kpos) h
    rw [←mul_assoc, ←mul_assoc, inv?_mul_cancel, one_mul, one_mul] at this
    assumption
  intro a b k kpos altb
  apply mul_lt_mul_of_pos_left
  assumption
  assumption

def le_iff_mul_le_mul_of_pos_right (a b k: α) (h: 0 < k) : a ≤ b ↔ a * k ≤ b * k := by
  apply le_iff_of_lt_iff
  apply lt_iff_mul_lt_mul_of_pos_right
  assumption

def le_iff_mul_le_mul_of_pos_left (a b k: α) (h: 0 < k) : a ≤ b ↔ k * a ≤ k * b := by
  apply le_iff_of_lt_iff
  apply lt_iff_mul_lt_mul_of_pos_left
  assumption

end

section

variable [SemifieldOps α] [IsNonCommSemifield α] [LE α] [LT α] [IsStrictOrderedSemiring α]
   [IsLinearOrder α]

def div?_pos (a b: α) (ha: 0 < a) (hb: 0 < b): 0 < a /? b := by
  rw [div?_eq_mul_inv?]
  apply mul_pos
  assumption
  apply inv?_pos
  assumption

def half_pos {ε: α} (h: 0 < ε) : 0 < ε /? 2 ~(((ne_of_lt two_pos).symm: (2: α) ≠ 0)) := by
  have := mul_lt_mul_of_pos_left _ _ (inv?_pos _ two_pos) _ h
  rw [mul_zero, ←div?_eq_mul_inv?] at this
  assumption

def add_half (a: α) : a /? 2 ~(by symm; apply ne_of_lt two_pos) + a /? 2 ~(by symm; apply ne_of_lt two_pos) = a := by
  rw [add_div?_add', ←mul_two, div?_eq_mul_inv?, mul_assoc, mul_inv?_cancel, mul_one]

variable [Min α] [Max α] [IsLinearMinMaxOrder α] [NeZero (2: α)]

def min_le_midpoint (a b: α) : min a b ≤ midpoint a b := by
  apply min_le_iff.mpr
  unfold midpoint
  rcases lt_or_le a b
  left; apply (le_iff_mul_le_mul_of_pos_right _ _ 2 _).mpr
  rw [div?_mul_cancel, mul_two]
  apply add_le_add_left
  apply le_of_lt; assumption
  apply two_pos
  right; apply (le_iff_mul_le_mul_of_pos_right _ _ 2 _).mpr
  rw [div?_mul_cancel, mul_two]
  apply add_le_add_right
  assumption
  exact two_pos

def midpoint_le_max (a b: α) : midpoint a b ≤ max a b := by
  apply le_max_iff.mpr
  unfold midpoint
  rcases lt_or_le b a
  left; apply (le_iff_mul_le_mul_of_pos_right _ _ 2 _).mpr
  rw [div?_mul_cancel, mul_two]
  apply add_le_add_left
  apply le_of_lt; assumption
  apply two_pos
  right; apply (le_iff_mul_le_mul_of_pos_right _ _ 2 _).mpr
  rw [div?_mul_cancel, mul_two]
  apply add_le_add_right
  assumption
  apply two_pos

end
