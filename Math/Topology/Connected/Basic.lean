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

def IsPreconnected.onSet (s: Set α) (hs: IsPreconnectedOn s) : IsPreconnected s where
  univ_preconnected := by
    rintro _ _ ⟨u, hu, rfl⟩  ⟨v, hv, rfl⟩ total ha hb
    simp at *
    obtain ⟨a, ha⟩ := ha
    obtain ⟨b, hb⟩ := hb
    have ⟨x, hx, meminter⟩ := hs u v hu hv ?_ ⟨a.val, a.property, ha⟩ ⟨b.val, b.property, hb⟩
    exists ⟨x, hx⟩
    intro x hx
    exact total ⟨x, hx⟩ True.intro

def IsPreconnected.ofSet (s: Set α) (hs: IsPreconnected s) : IsPreconnectedOn s := by
  intro u v hu hv total ⟨x, hx', hx⟩ ⟨y, hy', hy⟩
  have ⟨⟨z, hz⟩, hz'⟩ := hs.univ_preconnected (Set.mk fun x => x.val ∈ u) (Set.mk fun x => x.val ∈ v)  ?_ ?_ ?_ ?_ ?_
  exists z
  simp [Set.mem_inter]
  apply And.intro hz
  simp at hz'
  apply hz'
  exists u
  exists v
  intro ⟨z, hz⟩ _
  apply total
  assumption
  exists ⟨x, hx'⟩
  exists ⟨y, hy'⟩

def IsPreconnectedOn.not_split (s a b: Set α)
  (hs: IsPreconnectedOn s) (d: Disjoint a b) (sub_union: s ⊆ a ∪ b)
  (ha: IsOpen a) (hb: IsOpen b) : s ⊆ a ∨ s ⊆ b := by
  rcases Set.empty_or_nonempty (s ∩ a) with h | h
  right; intro x hx
  apply (sub_union x hx).resolve_left
  intro
  suffices x ∈ (∅: Set α) by contradiction
  rw [←h]; apply And.intro <;> assumption
  rcases Set.empty_or_nonempty (s ∩ b) with g | g
  left; intro x hx
  apply (sub_union x hx).resolve_right
  intro
  suffices x ∈ (∅: Set α) by contradiction
  rw [←g]; apply And.intro <;> assumption
  have : IsPreconnected s := IsPreconnected.onSet _ hs
  let C₁ : Set s := Set.mk fun x => x.val ∈ a
  let C₂ : Set s := Set.mk fun x => x.val ∈ b
  have ⟨x, _, x_in_a, x_in_b⟩ := this.univ_preconnected C₁ C₂ ?_ ?_ ?_ ?_ ?_
  have := d {x.val} ?_ ?_ x.val rfl
  contradiction
  rintro _ rfl; assumption
  rintro _ rfl; assumption
  exists a
  exists b
  intro x hx
  apply sub_union
  exact x.property
  simp; obtain ⟨x, x_in_s, hx⟩ := h
  exists ⟨x, x_in_s⟩
  simp; obtain ⟨x, x_in_s, hx⟩ := g
  exists ⟨x, x_in_s⟩

instance [IsPreconnected α] [IsPreconnected β] : IsPreconnected (α × β) where
  univ_preconnected := by
    intro U V hU hV total
    simp [Set.univ_inter]
    intro ⟨x, hx⟩ ⟨y, hy⟩
    rw [←Set.not_disjoint_iff_nonempty_inter]
    intro disjoint
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
    have preconn_slice_α' : ∀x: β, IsPreconnectedOn (Set.zip (⊤: Set α) {x}) := by
      intro b₀
      apply IsPreconnected.ofSet
      apply preconnected_of_ofHom (α := α × ({b₀}: Set β))
      clear x hx y hy total disjoint hU hV U V preconn_slice_α preconn_slice_β
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      intro (a, b); refine ⟨(a, b.val), ?_⟩
      simp [Set.mem_zip, Set.mem_univ, b.property]
      intro ⟨(a, b), hb⟩; refine (a, ⟨b, ?_⟩)
      exact hb.right
      intro; rfl
      intro; rfl
      simp
      apply IsContinuous.subtype_mk
      apply IsContinuous.prod_mk
      infer_instance
      apply IsContinuous.comp
      simp
      apply And.intro
      apply IsContinuous.comp
      apply IsContinuous.subtype_mk
      apply IsContinuous.comp
    have preconn_slice_β' : ∀x: α, IsPreconnectedOn (Set.zip {x} (⊤: Set β)) := by
      intro a₀
      apply IsPreconnected.ofSet
      apply preconnected_of_ofHom (α := ({a₀}: Set α) × β)
      clear x hx y hy total disjoint hU hV U V preconn_slice_α preconn_slice_β
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      intro (a, b); refine ⟨(a.val, b), ?_⟩
      simp [Set.mem_zip, Set.mem_univ, a.property]
      intro ⟨(a, b), ha⟩; refine (⟨a, ?_⟩, b)
      exact ha.left
      intro; rfl
      intro; rfl
      simp
      apply IsContinuous.subtype_mk
      apply IsContinuous.prod_mk
      apply IsContinuous.comp
      infer_instance
      simp
      apply And.intro
      apply IsContinuous.subtype_mk
      apply IsContinuous.comp
      apply IsContinuous.comp
    have α₀ : ∀x: α, (Set.zip {x} (⊤: Set β)) ⊆ U ∨ (Set.zip {x} (⊤: Set β)) ⊆ V := by
      intro x
      apply IsPreconnectedOn.not_split
      apply preconn_slice_β'
      assumption
      apply Set.sub_trans _ total
      apply Set.sub_univ
      assumption
      assumption
    have β₀: ∀x: β, (Set.zip (⊤: Set α) {x}) ⊆ U ∨ (Set.zip (⊤: Set α) {x}) ⊆ V := by
      intro x
      apply IsPreconnectedOn.not_split
      apply preconn_slice_α'
      assumption
      apply Set.sub_trans _ total
      apply Set.sub_univ
      assumption
      assumption
    suffices (∀x: α, Set.zip {x} (⊤: Set β) ⊆ U) ∨ (∀x: α, Set.zip {x} (⊤: Set β) ⊆ V) by
      rcases this with h | h
      have : U = ⊤ := by
        apply Set.ext_univ
        intro z
        apply h z.1
        apply And.intro
        rfl
        trivial
      rw [this] at disjoint
      have := disjoint {y} (Set.sub_univ _) ((Set.singleton_sub _ _).mpr hy) y rfl
      contradiction
      have : V = ⊤ := by
        apply Set.ext_univ
        intro z
        apply h z.1
        apply And.intro
        rfl
        trivial
      rw [this] at disjoint
      have := disjoint {x} ((Set.singleton_sub _ _).mpr hx) (Set.sub_univ _) x rfl
      contradiction
    apply Classical.or_iff_not_imp_left.mpr
    intro h a z ⟨rfl, hz⟩; clear hz
    clear a
    simp [Classical.not_forall] at h
    obtain ⟨a, ha⟩ := h
    have h₂ := (α₀ a).resolve_left ha (a, z.snd) ?_
    refine (β₀ z.snd).resolve_left ?_ z ?_
    intro h
    have g := (h (a, z.snd) ?_)
    have := disjoint _ ((Set.singleton_sub _ _).mpr g) ((Set.singleton_sub _ _).mpr h₂) _ rfl
    contradiction
    apply And.intro
    trivial
    rfl
    apply And.intro
    trivial
    rfl
    apply And.intro
    rfl
    trivial

instance [IsConnected α] [IsConnected β] : IsConnected (α × β) where

end Topology
