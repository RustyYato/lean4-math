import Math.Topology.MetricSpace.Basic
import Math.Data.Rat.OrderedAlgebra

instance : Dist ℚ ℚ where
  dist a b := ‖a - b‖

instance : IsMetricSpace ℚ where
  dist_self := by
    intro x
    show ‖_‖ = _
    rw [sub_self]
    rfl
  dist_comm := by
    intro a b
    show ‖_‖ = _
    rw [Rat.abs_sub_comm]
    rfl
  dist_triangle := by
    intro a b k
    show ‖_‖ ≤ ‖_‖ + ‖_‖
    rw [←sub_zero (a - b), ←sub_self k, sub_sub, sub_eq_add_neg a, add_assoc,
      add_comm a, sub_eq_add_neg, add_assoc, add_comm (-b), ←sub_eq_add_neg, ←sub_eq_add_neg, add_comm]
    apply Rat.abs_add_le_add_abs
  of_dist_eq_zero := by
    intro a b eq
    have := Rat.eq_zero_iff_abs_eq_zero.mpr eq
    exact eq_of_sub_eq_zero _ _ this

instance : Topology ℚ := Topology.ofIsPseudoMetricSpace
