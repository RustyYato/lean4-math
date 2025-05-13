import Math.Data.Cardinal.Order
import Math.Data.Rat.Basic

def card_rat : #ℚ = ℵ₀ := by
  apply le_antisymm
  refine ⟨?_⟩
  exact {
    toFun q :=
      let q := q.toFract
      ⟨Nat.pair (Equiv.nat_equiv_nat_sum_nat.symm (Equiv.int_equiv_nat_sum_nat q.1)) q.2⟩
    inj' := by
      intro a b eq
      simp at eq
      rw [Equiv.nat_equiv_nat_sum_nat.symm.inj.eq_iff,
        Equiv.int_equiv_nat_sum_nat.inj.eq_iff] at eq
      suffices a.toFract = b.toFract by
        rwa [Rat.toFract.inj] at this
      ext; exact eq.left; exact eq.right
  }
  refine ⟨?_⟩
  exact {
    toFun n := n.down
    inj' := HasChar.natCast_inj.comp (Equiv.ulift _).inj
  }
