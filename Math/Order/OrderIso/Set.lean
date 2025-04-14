import Math.Order.OrderIso
import Math.Data.Set.Basic

variable [LE α] [LE β]

def OrderEquiv.instIsLawfulSupSet (h: β ≃o α) [SupSet β] [SupSet α] [IsLawfulSupSet α]
  (hs: ∀s: Set β, ⨆ s = h.symm (⨆ (s.preimage h.symm))): IsLawfulSupSet β where
  le_sSup := by
    intro s x mem
    have : s.preimage id = s := rfl
    erw [←this, ←funext (g := id) h.coe_symm, ←Set.preimage_preimage]
    apply (map_le h).mpr
    rw [hs, h.symm_coe]
    apply le_sSup
    apply Set.mem_preimage.mpr
    rw [h.coe_symm, Set.preimage_preimage, Set.preimage_id']
    assumption
    intro
    simp [h.coe_symm]

def OrderEquiv.instIsLawfulInfSet (h: β ≃o α) [InfSet β] [InfSet α] [IsLawfulInfSet α]
  (hs: ∀s: Set β, ⨅ s = h.symm (⨅ (s.preimage h.symm))): IsLawfulInfSet β where
  sInf_le := by
    intro s x mem
    have : s.preimage id = s := rfl
    erw [←this, ←funext (g := id) h.coe_symm, ←Set.preimage_preimage]
    apply (map_le h).mpr
    rw [hs, h.symm_coe]
    apply sInf_le
    apply Set.mem_preimage.mpr
    rw [h.coe_symm, Set.preimage_preimage, Set.preimage_id']
    assumption
    intro
    simp [h.coe_symm]
