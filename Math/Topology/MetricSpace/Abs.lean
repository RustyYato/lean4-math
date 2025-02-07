import Math.Algebra.Order
import Math.Topology.MetricSpace.Defs

namespace Abs

variable (α: Type*)
  [AbsoluteValue α γ] [LT γ] [LE γ]
  [AddMonoidOps γ] [AddGroupOps α] [IsAddGroup α] [IsAddCommMagma α]
  [IsOrderedAddCommMonoid γ] [IsOrderedAbsAddGroup α] [IsLinearOrder γ]

scoped instance : Dist α γ where
  dist x y := ‖x - y‖

instance : IsMetricSpace α where
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
    exact eq_of_sub_eq_zero (abs_zero.mp eq)

end Abs
