import Math.Data.Fintype.Cases
import Math.Topology.Connected.Basic

namespace Topology

variable {α: ι -> Type*} [∀i, Topology (α i)] [∀i, IsPreconnected (α i)]
  [ft: Fintype ι]

instance : IsPreconnected (∀i, α i) := by
  induction ft using Fintype.typeInduction with
  | empty =>
    apply IsPreconnected.mk
    intro u v hu hv total ⟨x, _, hx⟩ ⟨y, _, hy⟩
    simp; exists nofun
    apply And.intro
    rwa [show nofun = x from Subsingleton.allEq _ _]
    rwa [show nofun = y from Subsingleton.allEq _ _]
  | option =>
    sorry
  | eqv =>
    rename_i ι₀ ι₁ hι _ _ topo preconn
    suffices (∀i: ι₀, α (hι i)) ≃ₜ (∀i: ι₁, α i) by
      apply preconnected_of_ofHom this
    sorry

-- instance [IsConnected α] [IsConnected β] : IsConnected (α × β) where

end Topology
