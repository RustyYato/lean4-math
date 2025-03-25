import Math.Topology.Basic
import Math.Data.Set.Disjoint

namespace Topology

variable [Topology α]

def IsPreconnectedOn (s: Set α) :=
  -- if we have a partition of s given by u and v
  -- such that s intersects both u and v
  -- then there is a point common to all three sets
  ∀u v : Set α, IsOpen u → IsOpen v → s ⊆ u ∪ v →
    (s ∩ u).Nonempty → (s ∩ v).Nonempty →
    (s ∩ (u ∩ v)).Nonempty

def IsConnectedOn (s: Set α) :=
  s.Nonempty ∧ IsPreconnectedOn s

protected def IsConnectedOn.Nonempty {s: Set α} (h: IsConnectedOn s) : s.Nonempty := h.left
protected def IsConnectedOn.IsPreconnectedOn {s: Set α} (h: IsConnectedOn s) : IsPreconnectedOn s := h.right

def IsConnectedOn_singleton {x} : IsConnectedOn ({x} : Set α) where
  left := ⟨_, rfl⟩
  right := by
    intro u v hu hb s hu hv
    obtain ⟨x, rfl, _⟩ := hu
    obtain ⟨x, rfl, _⟩ := hv
    exists x

theorem IsPreconnectedOn_singleton {x} : IsPreconnectedOn ({x} : Set α) :=
  IsConnectedOn_singleton.IsPreconnectedOn

class IsPreconnected (α: Type*) [Topology α] : Prop where
  univ_preconnected: IsPreconnectedOn (⊤: Set α)

class IsConnected (α: Type*) [Topology α] : Prop extends IsPreconnected α where
  nonempty: Nonempty α := by infer_instance

instance [h: IsConnected α] : Nonempty α := h.nonempty

def IsPreconnectedOn.closed_iff {s: Set α} :
  IsPreconnectedOn s ↔ ∀ t t': Set α, IsClosed t → IsClosed t' → s ⊆ t ∪ t' → (s ∩ t).Nonempty → (s ∩ t').Nonempty → (s ∩ (t ∩ t')).Nonempty := by
  apply Iff.intro
  · intro h u v hu hv g ⟨x, hxs, hxu⟩ ⟨y, hys, hyv⟩
    rw [←Set.not_disjoint_iff_nonempty_inter, ←Set.subset_compl_iff_disjoint_right, Set.compl_inter]
    intro g'
    have := (g' _ hxs).resolve_left (by simpa [Set.mem_compl] using hxu)
    have := (g' _ hys).resolve_right (by simpa [Set.mem_compl] using hyv)
    suffices s = ∅ by
      cases this
      contradiction
    apply Set.ext_empty
    have ⟨y, hy, _, _⟩ := h uᶜ vᶜ hu hv g' ?_ ?_
    rcases g _ hy with hy | hy
    contradiction
    contradiction
    exists y
    exists x
  · intro h u v hu hv g ⟨x, hxs, hxu⟩ ⟨y, hys, hyv⟩
    rw [←Set.not_disjoint_iff_nonempty_inter, ←Set.subset_compl_iff_disjoint_right, Set.compl_inter]
    intro g'
    have := (g' _ hxs).resolve_left (by simpa [Set.mem_compl] using hxu)
    have := (g' _ hys).resolve_right (by simpa [Set.mem_compl] using hyv)
    suffices s = ∅ by
      cases this
      contradiction
    apply Set.ext_empty
    have ⟨y, hy, _, _⟩ := h uᶜ vᶜ (by simpa [IsClosed, Set.compl_compl]) (by simpa [IsClosed, Set.compl_compl]) g' ?_ ?_
    rcases g _ hy with hy | hy
    contradiction
    contradiction
    exists y
    exists x

end Topology
