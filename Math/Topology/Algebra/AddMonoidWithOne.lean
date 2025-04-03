import Math.Algebra.AddMonoidWithOne.Defs
import Math.Topology.Algebra.Monoid

open Topology

section

variable {ι α: Type*} [Topology ι] [Topology α]

instance [AddMonoidWithOneOps α] [IsAddMonoidWithOne α] : IsContinuous (Nat.cast: ℕ -> α) := by
  exact IsContinuous.bot_dom Nat.cast

-- @[continuity]
def continuous_natCast [AddMonoidWithOneOps α] [IsAddMonoidWithOne α] (f: ι -> ℕ) (hf: IsContinuous f) : IsContinuous (fun i => (f i: α)) := by
  apply IsContinuous.comp

end
