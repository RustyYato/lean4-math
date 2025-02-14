import Math.Topology.MetricSpace.Abs
import Math.Topology.MetricSpace.Basic
import Math.Algebra.Impls.Real
import Math.Data.Real.OrderedAlgebra

instance : Dist ℝ ℝ := Abs.instDist _
instance : IsMetricSpace ℝ := Abs.instIsMetricSpace _
instance : Topology ℝ := Topology.ofIsPseudoMetricSpace
