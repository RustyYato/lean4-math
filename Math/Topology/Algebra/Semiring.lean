import Math.Algebra.Semiring.Defs
import Math.Topology.Algebra.AddMonoidWithOne

open Topology

section

variable (α: Type*) [Topology α]

class IsTopologicalSemiring [SemiringOps α] extends IsSemiring α, IsContinuousAdd α, IsContinuousMul α where
