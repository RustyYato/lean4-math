import Math.Data.Cardinal.Order
import Math.Data.Rat.Basic

def card_rat : #ℚ = ℵ₀ := by
  apply le_antisymm
  refine ⟨?_⟩
  exact {
    toFun q :=
      let q := q.toFract
      Nat.pair (Equiv.nat_equiv_nat_sum_nat.symm (Equiv.int_equiv_nat_sum_nat q.1)) q.2
    inj' := by
      intro a b eq
      dsimp at eq
      rw [Nat.pair_eq_pair] at eq
      obtain ⟨ha, hb⟩ := eq
      have := Equiv.inj _ (Equiv.inj _ ha)
      apply Rat.toFract.inj.mp
      ext  <;> assumption
  }
  refine ⟨?_⟩
  exact {
    toFun n := n
    inj' := HasChar.natCast_inj
  }
