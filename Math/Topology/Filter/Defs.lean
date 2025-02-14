import Math.Topology.Basic
import Math.Order.Filter.Basic

variable [Topology α]

open FilterBase Topology

namespace Topology

/-- a set is a neighborhood if it contains an open set around x
    and the set of all neighborhoods is a filter --/
def nhds (a: α) : Filter α :=
  iInf fun x: Set.mk (fun s: Set α => a ∈ s ∧ IsOpen s) => 𝓟 x.val

@[inherit_doc]
scoped notation "𝓝" => nhds

/-- The "neighborhood within" filter. Elements of `𝓝[s] x` are sets containing the
    intersection of `s` and a neighborhood of `x`. -/
def nhdsWithin (x : α) (s : Set α) : Filter α := 𝓝 x ⊓ 𝓟 s

@[inherit_doc]
scoped notation "𝓝[" s "] " x:100 => nhdsWithin x s

-- the limit of a filter, if it exists
noncomputable def lim [Nonempty α] (f: Filter α) : α :=
  Classical.epsilon fun x => f ≤ 𝓝 x

def lim_spec [Nonempty α] (f: Filter α) (h: ∃x, f ≤ 𝓝 x) : f ≤ 𝓝 (lim f) := Classical.epsilon_spec h

end Topology
