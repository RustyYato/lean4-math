import Math.Topology.Basic
import Math.Topology.MetricSpace.Defs
import Math.Algebra.Ring.Defs
import Math.Algebra.Semiring.Order.Defs

section

variable [LT β] [LE β] [IsNontrivial β] [AddMonoidOps β] [IsOrderedAddCommMonoid β]

instance : IsPreOrder β :=
  have := inferInstanceAs (IsPartialOrder β)
  this.toIsPreOrder

def Ball [Dist α β] (x: α) (δ: β): Set α := Set.mk fun y => dist x y < δ

def mem_ball {_: Dist α β} {c: α} {δ: β} : ∀{x}, x ∈ Ball c δ ↔ dist c x < δ := Iff.rfl

def ball_sub {_: Dist α β} (x: α) (δ₀ δ₁: β) (h: δ₀ ≤ δ₁) : Ball x δ₀ ⊆ Ball x δ₁ := by
  intro y mem
  apply lt_of_lt_of_le
  assumption
  assumption

end

namespace IsPseudoMetric

variable [LT β] [LE β] [IsNontrivial β] [SemiringOps β] [IsOrderedSemiring β]
   [Dist α β] [IsLinearOrder β] [IsPseudoMetric α]

def toTopology : Topology α where
  -- a set is open if, forall points in the set, there is a ball with positive radius
  -- that is contained in the set
  IsOpen s := ∀x ∈ s, ∃δ > 0, Ball x δ ⊆ s
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
    apply ball_sub _ _ _ _ _ mem
    split
    rfl
    apply le_of_not_le
    assumption
    apply ball_b_sub
    apply ball_sub _ _ _ _ _ mem
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

end IsPseudoMetric

namespace Topology

section

variable (α: Type*) [LT β] [LE β] [IsNontrivial β] [SemiringOps β] [IsOrderedSemiring β]
   [Dist α β] [IsLinearOrder β] [t: Topology α]

class IsPseudoMetricSpace: Prop extends IsPseudoMetric α where
  open_iff_contains_ball: ∀s: Set α, IsOpen s ↔ ∀x ∈ s, ∃δ > 0, Ball x δ ⊆ s

class IsMetricSpace: Prop extends IsMetric α, IsPseudoMetricSpace α where

def open_iff_contains_ball [IsPseudoMetricSpace α] : ∀s: Set α, IsOpen s ↔ ∀x ∈ s, ∃δ > 0, Ball x δ ⊆ s :=
  IsPseudoMetricSpace.open_iff_contains_ball

def metric_eq_topology [IsPseudoMetricSpace α] : t = IsPseudoMetric.toTopology := by
  ext
  apply open_iff_contains_ball

end

section

variable [LT β] [LE β] [IsNontrivial β] [RingOps β] [IsOrderedSemiring β]
  [IsRing β] [Dist α β] [IsLinearOrder β] [IsMetric α]
  [Topology α] [IsMetricSpace α]

def IsOpen.Ball: IsOpen (α := α) (Ball x δ) := by
  rw [metric_eq_topology (α := α)]
  intro y hy
  exists δ - dist x y
  apply And.intro
  have := add_lt_add_of_lt_of_le (dist x y) (-dist x y) δ (-dist x y) ?_ (le_refl _)
  rw [add_neg_cancel, ←sub_eq_add_neg] at this
  assumption
  assumption
  intro z hz
  replace hz: dist y z < _ := hz
  show dist x z < δ
  apply lt_of_le_of_lt
  apply dist_triangle _ _ y
  apply lt_of_lt_of_le
  exact add_lt_add_of_le_of_lt (dist x y) (dist y z) (dist x y) (δ - dist x y) (le_refl _) hz
  rw [add_comm, sub_add_cancel]

end

end Topology
