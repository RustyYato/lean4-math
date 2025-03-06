import Math.Algebra.Group.Theory.Basic
import Math.Algebra.Impls.Fin
import Math.Algebra.Group.SetLike.Basic
import Math.Order.OrderIso

-- the cyclic group of order n
instance Cyclic (n: ℕ) [h: NeZero n] : Group (Fin n) := by
  match n, h with
  | n + 1, h =>
  apply Group.ofAdd

namespace Cyclic

variable {n: ℕ} [NeZero n]

def npow_n_eq_one (a: Cyclic n) : a ^ n = 1 := by
  rename_i h
  match n, h with
  | n + 1, h =>
  apply HasChar.char_spec (Fin (n + 1))

def sub_cyclic_eq_generate (S: Subgroup (Cyclic n)) : ∃x: Cyclic n, S = Subgroup.generate {x} := by
  rename_i h
  match n, h with
  | n + 1, h =>
  have ⟨m, ⟨m_pos, m_le_n_succ, m_spec⟩, m_min⟩ := Relation.exists_min (α := Nat) (· < ·) (P := fun x => 0 < x ∧ x ≤ n+1 ∧ ∀a' ∈ S, a' ^ x = 1) ⟨n+1, Nat.zero_lt_succ _, Nat.le_refl _, by
    intros
    rename_i a' _
    apply HasChar.char_spec (Fin (n + 1))⟩
  sorry

def sub_cylic (G: Subgroup (Cyclic n)) : ∃m, Nonempty (G ≃* Cyclic (m + 1)) := by
  sorry

end Cyclic
