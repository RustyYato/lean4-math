import Math.Topology.Basic
import Math.Topology.MetricSpace.Defs

variable
  [LT β] [LE β] [Zero β] [One β] [IsNontrivial β] [Add β] [SMul ℕ β] [Mul β] [Pow β ℕ] [NatCast β] [∀n, OfNat β (n + 2)]
  [IsOrderedSemiring β]
  [Dist α β]

namespace IsPseudoMetricSpace

def Ball (x: α) (δ: β): Set α := Set.mk fun y => dist x y < δ

def ball_sub (x: α) (δ₀ δ₁: β) (h: δ₀ ≤ δ₁) : Ball x δ₀ ⊆ Ball x δ₁ := by
  intro y mem
  apply lt_of_lt_of_le
  assumption
  assumption

end IsPseudoMetricSpace

namespace Topology

def ofIsPseudoMetricSpace [IsPseudoMetricSpace α] : Topology α where
  -- a set is open if, forall points in the set, there is a ball with positive radius
  -- that is contained in the set
  IsOpen s := ∀x ∈ s, ∃δ > 0, IsPseudoMetricSpace.Ball x δ ⊆ s
  univ_open := by
    dsimp
    intro x mem
    exists 1
    apply And.intro
    apply zero_lt_one
    apply Set.sub_univ
  inter_open := by
    classical
    intro a b ha hb
    intro x ⟨xa, xb⟩
    have ⟨da, da_pos, ball_a_sub⟩ := ha _ xa
    have ⟨db, db_pos, ball_b_sub⟩ := hb _ xb
    exists if da ≤ db then da else db
    apply And.intro
    split <;> assumption
    intro x mem
    apply And.intro
    apply ball_a_sub
    apply IsPseudoMetricSpace.ball_sub _ _ _ _ _ mem
    split
    rfl
    apply le_of_not_le
    assumption
    apply ball_b_sub
    apply IsPseudoMetricSpace.ball_sub _ _ _ _ _ mem
    split
    assumption
    rfl
  sUnion_open := by
    intro S h x ⟨s, s_in_S, x_in_s⟩
    replace ⟨d, d_pos, h⟩  := h _ s_in_S x x_in_s
    refine ⟨_, d_pos, ?_⟩
    apply Set.sub_trans h
    apply Set.sub_sUnion
    assumption

end Topology
