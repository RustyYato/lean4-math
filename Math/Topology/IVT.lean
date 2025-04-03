import Math.Order.Filter.TopBot
import Math.Topology.Filter.Defs
import Math.Topology.Connected.Basic
import Math.Topology.Order.Defs

namespace Topology

def intermediate_value_univ₂
  [Topology X] [Topology α] [LE α] [LT α] [IsLinearOrder α]
  [IsPreconnected X] [IsOrderClosed α]
  {a b : X} {f g : X → α} (hf : IsContinuous f)
  (hg : IsContinuous g) (ha : f a ≤ g a) (hb : g b ≤ f b) : ∃ x, f x = g x := by
  obtain ⟨x, _, hfg, hgf⟩ : (⊤ ∩ Set.mk (fun x => f x ≤ g x ∧ g x ≤ f x)).Nonempty :=
    IsPreconnectedOn.closed_iff.1 IsPreconnected.univ_preconnected _ _ (Topology.isClosed_le hf hg) (Topology.isClosed_le hg hf) (fun _ _ => le_total (α := α) _ _) ⟨a, by trivial, ha⟩ ⟨b, by trivial, hb⟩
  exact ⟨x, le_antisymm hfg hgf⟩

def intermediate_value_univ
  [Topology X] [Topology α]
  [OrderOps α] [IsLinearOrder α] [IsOrderClosed α]
  [IsPreconnected X] (a b : X) {f : X → α} (hf : IsContinuous f) :
  Set.Icc (f a) (f b) ⊆ Set.range f := by
    intro x hx
    apply intermediate_value_univ₂
    continuity
    continuity
    exact hx.right
    exact hx.left

def mem_range_of_exists_le_of_exists_ge
  [Topology X] [Topology α]
  [OrderOps α] [IsLinearOrder α] [IsOrderClosed α]
  [IsPreconnected X] {c : α} {f : X → α}
    (hf : IsContinuous f) (h₁ : ∃ a, f a ≤ c) (h₂ : ∃ b, c ≤ f b) : c ∈ Set.range f :=
  let ⟨a, ha⟩ := h₁; let ⟨b, hb⟩ := h₂; intermediate_value_univ a b hf _ ⟨ha, hb⟩

def surjective
  [Topology X] [Topology α]
  [Nonempty X] [LatticeOps X] [IsLattice X]
  [OrderOps α] [IsLinearOrder α]
  [IsPreconnected X] [IsOrderClosed α]
  (f: X -> α) (hf: IsContinuous f)
  (top: Filter.TendsTo f .atTop .atTop)
  (bot: Filter.TendsTo f .atBot .atBot):
  Function.Surjective f := by
  intro x
  apply mem_range_of_exists_le_of_exists_ge
  continuity
  exact (bot.eventually (Filter.eventually_le_atBot x)).exists
  exact (top.eventually (Filter.eventually_ge_atTop x)).exists

end Topology
