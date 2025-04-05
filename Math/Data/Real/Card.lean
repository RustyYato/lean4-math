import Math.Data.Real.Order
import Math.Data.Cardinal.Order
import Math.Data.Set.Order.Interval

def card_zero_to_one_eq_card_one_lt : #(Set.Ioo (0: ℝ) 1) = #(Set.Ioi (1: ℝ)) := by
  apply Quotient.sound
  refine ⟨{
    toFun := ?_
    invFun := ?_
    leftInv := ?_
    rightInv := ?_
  }⟩
  intro ⟨x, h, g⟩
  refine ⟨x⁻¹?, ?_⟩
  show 1 < x⁻¹?
  replace h : 0 < x := h
  replace g : x < 1 := g
  have := mul_lt_mul_of_pos_left _ _ g _ (inv?_pos _ h)
  rw [inv?_mul_cancel, mul_one] at this
  assumption
  intro ⟨x, h⟩
  replace h : 1 < x := h
  have : 0 < x := lt_trans zero_lt_one h
  refine ⟨x⁻¹?, ?_, ?_⟩
  apply inv?_pos x
  assumption
  show x⁻¹? < 1
  have := mul_lt_mul_of_pos_left _ _ h _ (inv?_pos _ this)
  rw [mul_one, inv?_mul_cancel] at this
  assumption
  intro ⟨x, _, _⟩
  dsimp; congr
  apply inv?_inv?
  intro ⟨x, _⟩
  dsimp; congr
  apply inv?_inv?

def card_one_lt_eq_card_real : #(Set.Ioi (1: ℝ)) = #ℝ := by
  apply le_antisymm
  exact ⟨Embedding.subtypeVal⟩
  refine ⟨{
    toFun x := ⟨?_, ?_⟩
    inj' := ?_
  }⟩
  · sorry
  · rw [Set.mem_Ioi]
    sorry
  · sorry
