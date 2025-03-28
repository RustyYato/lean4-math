import Math.Algebra.Ring.Defs
import Math.Topology.Algebra.AddGroupWithOne
import Math.Topology.Algebra.Semiring

open Topology

section

variable (α: Type*) [Topology α]

class IsTopologicalRing [RingOps α] extends IsRing α, IsTopologicalSemiring α, IsContinuousNeg α where
