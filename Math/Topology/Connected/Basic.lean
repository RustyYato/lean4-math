import Math.Topology.Hom
import Math.Data.Set.Disjoint

namespace Topology

variable [Topology α] [Topology β]

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

def preconnected_of_ofHom [IsPreconnected α] (h: α ≃ₜ β) : IsPreconnected β where
  univ_preconnected := by
    intro u v hu hv total hx hy
    have partition : ⊤ = u.preimage h ∪ v.preimage h := by
      symm
      apply Set.ext_univ
      intro x
      simp [Set.mem_preimage, Set.mem_union]
      apply total
      trivial
    have := IsPreconnected.univ_preconnected (u.preimage h) (v.preimage h)
      (IsOpen.preimage h _ hu) (IsOpen.preimage h _ hv) (by rw [partition])
    simp [Set.univ_inter] at *
    replace ⟨x, g₀, g₁⟩ := this ?_ ?_
    exists h x
    obtain ⟨x, hx⟩ := hx
    exists h.symm x
    rwa [Set.mem_preimage, h.symm_coe]
    obtain ⟨x, hx⟩ := hy
    exists h.symm x
    rwa [Set.mem_preimage, h.symm_coe]

def connected_of_ofHom [IsConnected α] (h: α ≃ₜ β) : IsConnected β :=
  have : Nonempty β := h.Nonempty
  { preconnected_of_ofHom h with }

instance [IsPreconnected α] [IsPreconnected β] : IsPreconnected (α × β) where
  univ_preconnected := by
    intro U V hU hV total
    simp [Set.univ_inter]
    intro ⟨x, hx⟩ ⟨y, hy⟩
    rw [←Set.not_disjoint_iff_nonempty_inter]
    intro disjoint
    rw [←Set.subset_compl_iff_disjoint_right] at disjoint
    have preconn_slice_α : ∀x: β, IsPreconnected (α × ({x}: Set β)) := by
      intro x
      let α' := α × ({x}: Set β)
      let α'_iso_α : α' ≃ₜ α := Iso.subsing_prod_right
      exact preconnected_of_ofHom α'_iso_α.symm
    have preconn_slice_β : ∀x: α, IsPreconnected (({x}: Set α) × β) := by
      intro x
      let β' := ({x}: Set α) × β
      let β'_iso_β : β' ≃ₜ β := Iso.subsing_prod_left
      exact preconnected_of_ofHom β'_iso_β.symm
    suffices U = ⊤ ∨ V = ⊤ by
      rcases this with rfl | rfl
      exact disjoint y (by trivial) hy
      exact disjoint x hx (by trivial)
    clear disjoint
    apply Classical.or_iff_not_imp_left.mpr
    intro h
    have ⟨z, hz⟩ := Set.compl_nonempty_of_ne_top _ h
    clear h
    apply Set.ext_univ
    intro v
    sorry

instance [IsConnected α] [IsConnected β] : IsConnected (α × β) where

end Topology
