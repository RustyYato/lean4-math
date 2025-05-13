import Math.Topology.Separable.Defs

open Filter FilterBase

namespace Topology

variable {X Y: Type*} [Topology X] [Topology Y]

def tendsto_nhds_unique_inseparable [R1 X] {f : Y → X} {l : Filter Y} {a b : X} [FilterBase.NeBot l]
    (ha : TendsTo f l (𝓝 a)) (hb : TendsTo f l (𝓝 b)) : Inseparable a b :=
  Inseparable.of_nhds_neBot <| neBot_of_le <| le_min ha hb

def tendsto_nhds_unique [T2 X] {f : Y → X} {l : Filter Y} {a b : X} [NeBot l]
    (ha : TendsTo f l (𝓝 a)) (hb : TendsTo f l (𝓝 b)) : a = b :=
    (tendsto_nhds_unique_inseparable ha hb).eq

def lim_eq [T2 X] {x : X} [NeBot f] (h : f ≤ 𝓝 x) : @lim _ _ ⟨x⟩ f = x := by
  apply tendsto_nhds_unique _ h
  have : Nonempty X := ⟨x⟩
  apply lim_spec
  exists x

def lim_eq' [T2 X] (f: Filter X) [f.NeBot] (o: X) : (∀s: Set X, Topology.IsOpen s -> o ∈ s -> f ≤ FilterBase.principal s) ->
  @lim _ _ ⟨o⟩ f = o := by
  intro spec
  apply Topology.lim_eq
  intro S h
  induction h with
  | up =>
    apply FilterBase.closed_upward
    assumption
    assumption
  | min =>
    apply FilterBase.closed_min
    assumption
    assumption
  | basic hx =>
    rename_i x
    rcases hx with hx | hx
    subst hx
    apply Filter.univ_mem
    replace hx := Set.mem_sUnion.mp hx
    obtain ⟨U, hU, hx⟩ := hx
    simp [Set.mem_image, Set.mem_range] at hU
    obtain ⟨_, ⟨s, ⟨_, sopen⟩, rfl⟩, rfl⟩ := hU
    apply spec
    repeat assumption


end Topology
