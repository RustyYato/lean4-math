import Math.Topology.MetricSpace.Basic
import Math.Algebra.Norm.Basic

namespace Norm

variable (α: Type*) {γ: Type*}
  [Norm α γ] [LatticeOps γ] [SemiringOps γ] [IsSemiring γ]
  [AddGroupOps α] [IsAddGroup α] [IsAddCommMagma α]
  [IsOrderedSemiring γ] [IsLinearLattice γ] [IsNontrivial γ] [IsLawfulNorm α]

scoped instance : Dist α γ where
  dist x y := ‖x - y‖

instance : IsMetric α where
  dist_self := by
    intro x
    dsimp [dist]
    rw [sub_self, norm_zero]
  dist_comm := by
    intro x y
    simp [dist]
    rw [norm_sub_comm]
  dist_triangle := by
    intro x y k
    dsimp [dist]
    rw [←add_zero (x - y), ←sub_self k,
      sub_eq_add_neg, sub_eq_add_neg, ←add_assoc,
      add_assoc x, add_assoc x, add_comm _ (-k),
      ←add_assoc, add_comm _ k, ←sub_eq_add_neg,
      ←sub_eq_add_neg]
    apply norm_add_le_add_norm
  of_dist_eq_zero := by
    intro x y eq
    dsimp [dist] at eq
    exact eq_of_sub_eq_zero (of_norm_eq_zero eq)

scoped instance : Topology α := IsPseudoMetric.toTopology

instance : Topology.IsMetricSpace α where
  open_iff_contains_ball _ := Iff.rfl

end Norm
