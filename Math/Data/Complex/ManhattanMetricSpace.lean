import Math.Algebra.Impls.Complex
import Math.Data.Real.MetricSpace
import Math.Topology.Separable.Defs

namespace Complex

namespace ManhattanMetric

open Topology

/- These instance is scoped because it isn't the standard topology on Complex numbers
  But defining the standard topology requires sqrt, which isn't defined yet, so
  we use the manhattan metric as a stand in to prove properties of exp and then in
  turn sqrt. After which we will define the standard topology for complex numbers.
 -/

instance : Dist ℂ ℝ where
  dist a b := ‖a.real - b.real‖ + ‖a.img - b.img‖

instance manhattanMetricSpace : IsMetricSpace ℂ where
  dist_comm x y := by simp [dist, abs_sub_comm]
  dist_self x := by simp [dist, abs_zero.mpr rfl]
  dist_triangle a b c := by
    simp [dist]
    rw [add_assoc, add_left_comm ‖a.img - c.img‖, ←add_assoc]
    apply add_le_add
    apply dist_triangle (α := ℝ)
    apply dist_triangle (α := ℝ)
  of_dist_eq_zero x y h := by
    simp [dist] at h
    suffices ‖x.real - y.real‖ = 0 by
      rw [this, zero_add] at h
      ext
      apply of_dist_eq_zero
      assumption
      apply of_dist_eq_zero
      assumption
    apply flip le_antisymm
    apply IsLawfulAbs.abs_nonneg
    rw [add_eq_iff_eq_sub, zero_sub] at h
    rw [h, ←neg_le_neg_iff, neg_neg]
    apply IsLawfulAbs.abs_nonneg

scoped instance : Topology ℂ := Topology.ofIsPseudoMetricSpace

instance : Topology.T0 ℂ where
  proof := by
    intro a b h
    have : {a} ∈ 𝓝 a := by
      rw [mem_nhds]
      refine ⟨{a}, Set.sub_refl _, ?_, rfl⟩
      rintro x rfl



      sorry
    sorry

end ManhattanMetric

end Complex
