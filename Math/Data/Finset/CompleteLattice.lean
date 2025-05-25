import Math.Order.Lattice.Complete
import Math.Data.Finset.Lattice


noncomputable section

namespace Finset

open Classical

variable [Fintype α]

instance : InfSet (Finset α) where
  sInf S := (Finset.univ α).filter <| fun x => ∀f ∈ S, x ∈ f

instance : SupSet (Finset α) where
  sSup S := (Finset.univ α).filter <| fun x => ∃f ∈ S, x ∈ f

attribute [local simp] sSup sInf mem_filter mem_univ

instance : IsCompleteLattice (Finset α) where
  le_sSup := by
    intro S f hf x hx
    simp
    exists f
  sSup_le := by
    intro f S h x mem
    simp at mem
    obtain ⟨f', _, _⟩ := mem
    apply h
    assumption
    assumption
  sInf_le := by
    intro S f hf x hx
    simp at hx
    apply hx
    assumption
  le_sInf := by
    intro f S h x hx
    simp
    intro f' hf'
    apply h
    assumption
    assumption

end Finset

end
