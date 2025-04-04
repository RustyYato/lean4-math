import Math.Topology.Constructions
import Math.Topology.MetricSpace.Defs
import Math.Algebra.Ring.Defs
import Math.Algebra.Semiring.Order.Defs

-- FIXME: split out constructions into it's own file or make MetricSpace/Abs only depend on
-- MetricSpace/Defs

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
   [Dist α β] [IsLinearOrder β]

class IsPseudoMetricSpace [t: Topology α]: Prop extends IsPseudoMetric α where
  open_iff_contains_ball: ∀s: Set α, IsOpen s ↔ ∀x ∈ s, ∃δ > 0, Ball x δ ⊆ s

class IsMetricSpace [t: Topology α]: Prop extends IsMetric α, IsPseudoMetricSpace α where

def open_iff_contains_ball [t: Topology α] [IsPseudoMetricSpace α] : ∀s: Set α, IsOpen s ↔ ∀x ∈ s, ∃δ > 0, Ball x δ ⊆ s :=
  IsPseudoMetricSpace.open_iff_contains_ball

def topology_eq_metric [t: Topology α] [IsPseudoMetricSpace α] : t = IsPseudoMetric.toTopology := by
  ext
  apply open_iff_contains_ball

end

section

variable [LT β] [LE β] [IsNontrivial β] [RingOps β] [IsOrderedSemiring β]
  [IsRing β] [Dist α β] [IsLinearOrder β]
  [Topology α] [instMetricSpace: IsPseudoMetricSpace α]

protected def IsOpen.Ball: IsOpen (α := α) (Ball x δ) := by
  rw [topology_eq_metric (α := α)]
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

def IsOpen.eq_sunion_balls (hS: IsOpen S) : S = ⋃(Set.mk fun s: Set α => (∃x r, s = Ball x r) ∧ s ⊆ S) := by
  rw [topology_eq_metric α] at hS
  ext x
  simp [Set.mem_sUnion]
  apply Iff.intro
  intro hx
  have ⟨δ, δpos, ball_sub⟩ := hS _ hx
  exists Ball x δ
  apply And.intro
  apply And.intro
  exists x
  exists δ
  assumption
  rwa [mem_ball, dist_self]
  intro ⟨_, ⟨⟨x, δ, rfl⟩, ball_sub_s⟩, hx⟩
  apply ball_sub_s
  assumption

end

end Topology

namespace Topology

variable {α β γ: Type*}
  [LT γ] [LE γ] [IsNontrivial γ] [RingOps γ] [IsOrderedSemiring γ]
  [IsRing γ] [Dist α γ] [Dist β γ] [Min γ] [Max γ] [IsLinearLattice γ]
  [ta: Topology α] [tb: Topology β]

section IsPseudoMetricSpace

variable [IsPseudoMetricSpace α] [IsPseudoMetricSpace β]

instance : IsContinuous' (α := α × β) (β := α) IsPseudoMetric.toTopology ta Prod.fst := by
  apply IsContinuous'.mk
  rw [topology_eq_metric α]
  intro S hS (a, b) ha
  replace ha : a ∈ S := ha
  have ⟨δ, δpos, ball⟩ := hS _ ha
  refine ⟨_, δpos, ?_⟩
  intro (c, d) hx
  show c ∈ S
  apply ball
  replace hx :  max _ _ < δ := hx
  exact (max_lt_iff.mp hx).left

instance : IsContinuous' (α := α × β) (β := β) IsPseudoMetric.toTopology tb Prod.snd := by
  apply IsContinuous'.mk
  rw [topology_eq_metric β]
  intro S hS (a, b) hb
  replace ha : b ∈ S := hb
  have ⟨δ, δpos, ball⟩ := hS _ hb
  refine ⟨_, δpos, ?_⟩
  intro (c, d) hx
  show d ∈ S
  apply ball
  replace hx :  max _ _ < δ := hx
  exact (max_lt_iff.mp hx).right

instance instProdIsPseudoMetricSpace : IsPseudoMetricSpace (α × β) where
  open_iff_contains_ball S := by
    let t': Topology (α × β) := IsPseudoMetric.toTopology
    show _ ↔ IsOpen[t'] _
    apply Iff.intro
    · intro h
      induction h with
      | univ => apply @IsOpen.univ _ t'
      | inter => apply @IsOpen.inter _ t' <;> assumption
      | sUnion => apply @IsOpen.sUnion _ t' <;> assumption
      | of  =>
        rename_i x hx
        simp at hx
        rcases hx with ⟨t,ht,rfl⟩ | ⟨t,ht,rfl⟩
        apply IsOpen.preimage
        assumption
        apply IsOpen.preimage
        assumption
    · intro hS
      have : S = ⋃(Set.mk fun s: Set (α × β) => (∃x r, s = Ball x r) ∧ s ⊆ S) := by
        ext x
        simp [Set.mem_sUnion]
        apply Iff.intro
        intro hx
        have ⟨δ, δpos, ball_sub⟩ := hS _ hx
        exists Ball x δ
        apply And.intro
        apply And.intro
        exists x.1
        exists x.2
        exists δ
        assumption
        rwa [mem_ball, dist_self]
        intro ⟨_, ⟨⟨a, b, δ, rfl⟩, ball_sub_s⟩, hx⟩
        apply ball_sub_s
        assumption
      rw [this]; clear this
      apply Topology.topo_product.sUnion_open
      rintro _ ⟨⟨x, δ, rfl⟩, hb⟩
      rw [show Ball x δ =
        (Set.mk fun y => dist x.fst y.fst < δ) ∩
        (Set.mk fun y => dist x.snd y.snd < δ)
        from ?_]
      apply Generate.IsOpen.inter
      · apply Generate.IsOpen.of
        left
        refine ⟨Ball x.1 δ, ?_, ?_⟩
        apply IsOpen.Ball
        rfl

      · apply Generate.IsOpen.of
        right
        refine ⟨Ball x.2 δ, ?_, ?_⟩
        apply IsOpen.Ball
        rfl

      ext y
      simp [mem_ball, Set.mem_inter]
      apply max_lt_iff

end IsPseudoMetricSpace

section IsMetricSpace

instance [IsMetricSpace α] [IsMetricSpace β] : IsMetricSpace (α × β) := {
  Prod.metricMax, instProdIsPseudoMetricSpace with
}

end IsMetricSpace

end Topology
