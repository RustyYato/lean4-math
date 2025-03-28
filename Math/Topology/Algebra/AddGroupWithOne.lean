import Math.Algebra.AddGroupWithOne.Defs
import Math.Topology.Algebra.AddMonoidWithOne
import Math.Topology.Algebra.Group

open Topology

section

variable {ι α: Type*} [Topology ι] [Topology α]

instance [AddGroupWithOneOps α] [IsAddGroupWithOne α] : IsContinuous (Int.cast: ℤ -> α) := by
  exact IsContinuous.bot_dom Int.cast

@[continuity]
def continuous_intCast [AddGroupWithOneOps α] [IsAddGroupWithOne α] (f: ι -> ℤ) (hf: IsContinuous f) : IsContinuous (fun i => (f i: α)) := by
  apply IsContinuous.comp

end
