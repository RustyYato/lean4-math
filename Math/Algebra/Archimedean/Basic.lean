import Math.Algebra.Order
import Math.Algebra.Field.Basic

class Archimedean (α) [AddMonoidOps α] [LT α] [LE α] [IsOrderedAddCommMonoid α] : Prop where
  /-- For any two elements `x`, `y` such that `0 < y`, there exists a natural number `n`
  such that `x ≤ n • y`. -/
  arch : ∀ (x : α) {y : α}, 0 < y → ∃ n : ℕ, x ≤ n • y

section Field

 variable [FieldOps α] [IsField α] [LT α] [LE α] [IsOrderedRing α]

def archimedean_iff_nat_lt : Archimedean α ↔ ∀ x : α, ∃ n : ℕ, x < n := by
  apply Iff.intro
  intro ⟨h⟩ x
  have ⟨n, x_le⟩ := h x (y := 1) zero_lt_one
  rw [←natCast_eq_nsmul_one] at x_le
  exists n+1
  apply lt_of_le_of_lt x_le
  apply lt_of_le_of_ne
  rw [natCast_succ]
  rw (occs := [1]) [←add_zero (n: α)]
  apply add_le_add_left
  exact zero_le_one
  intro g
  have : (n: α) - n = ((n + 1: ℕ): α) - n := by rw [g]
  rw [sub_self, natCast_add, add_comm, add_sub_assoc, sub_self, add_zero,
    natCast_one] at this
  exact zero_ne_one _ this
  intro h
  refine ⟨?_⟩
  intro x y ypos
  have ⟨n, eq⟩ := h (x /? y)
  exists n
  rw [←natCast_mul_eq_nsmul]
  have := mul_lt_mul_of_pos_right _ _ eq y ypos
  rw [div?_mul_cancel] at this
  apply le_of_lt; assumption

end Field
