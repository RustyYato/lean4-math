import Math.Topology.Basic
import Math.Data.Real.MetricSpace
import Math.Data.NNReal.Basic

instance : Topology ℝ≥0 := inferInstanceAs (Topology (Subtype _))
