import Math.Topology.Basic
import Math.Data.Real.MetricSpace
import Math.Data.NNReal.Basic

instance : Topology ℝ≥0 := inferInstanceAs (Topology (Subtype _))

instance : IsTopologicalSemiring ℝ≥0 where
  continuous_add := by
    apply Topology.IsContinuous.subtype_mk
    continuity
  continuous_mul := by
    apply Topology.IsContinuous.subtype_mk
    continuity
