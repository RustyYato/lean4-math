import Math.Topology.MetricSpace.Basic
import Math.Algebra.Abs.Basic

namespace Abs

variable (α: Type*) {γ: Type*}
  [LT γ] [LE γ] [IsNontrivial γ] [SemiringOps γ] [IsOrderedSemiring γ]
  [IsLinearOrder γ]
  [AddGroupOps α] [Mul α]
  [IsNonUnitalNonAssocRing α] [IsAddCommMagma α]
  [AbsoluteValue α γ] [IsLawfulAbs α]


scoped instance : Dist α γ where
  dist x y := |x - y|

instance : IsMetric α where
  dist_self := by
    intro x
    dsimp [dist]
    rw [sub_self, abs_zero]
  dist_comm := by
    intro x y
    simp [dist]
    rw [abs_sub_comm]
  dist_triangle := by
    intro x y k
    dsimp [dist]
    rw [←add_zero (x - y), ←sub_self k,
      sub_eq_add_neg, sub_eq_add_neg, ←add_assoc,
      add_assoc x, add_assoc x, add_comm _ (-k),
      ←add_assoc, add_comm _ k, ←sub_eq_add_neg,
      ←sub_eq_add_neg]
    apply abs_add_le_add_abs
  of_dist_eq_zero := by
    intro x y eq
    dsimp [dist] at eq
    exact eq_of_sub_eq_zero (of_abs_eq_zero eq)

scoped instance : Topology α := IsPseudoMetric.toTopology

instance : Topology.IsMetricSpace α where
  open_iff_contains_ball _ := Iff.rfl

end Abs
