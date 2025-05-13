import Math.Topology.Basic
import Math.Data.Set.Finite

namespace Topology

variable [Topology α]

def IsOpen.sInter (U: Set (Set α)) (hU: ∀u ∈ U, IsOpen u) [U.IsFinite] : IsOpen (⋂ U) := by
  induction U using Set.IsFinite.induction with
  | nil => simp; apply IsOpen.univ
  | cons a as a_notin_as as_finite ih =>
    simp
    apply IsOpen.inter
    apply hU
    simp
    apply ih
    intro u hu
    apply hU
    simp [hu]

end Topology
