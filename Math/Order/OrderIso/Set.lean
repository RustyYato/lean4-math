import Math.Order.OrderIso
import Math.Data.Set.Basic

variable [LE α] [LE β]

def OrderIso.instIsLawfulSupSet (h: β ≃o α) [SupSet β] [SupSet α] [IsLawfulSupSet α]
  (hs: ∀s: Set β, sSup s = h.symm (sSup (s.preimage h.symm))): IsLawfulSupSet β where
  le_sSup := by
    intro s x mem
    have : s.preimage id = s := rfl
    erw [←this, ←funext (g := id) h.coe_symm, ←Set.preimage_preimage]
    apply h.resp_le.mpr
    rw [hs, h.symm_coe]
    apply le_sSup
    apply Set.mem_preimage.mpr
    rw [h.coe_symm, Set.preimage_preimage, Set.preimage_id']
    assumption
    intro
    simp [h.coe_symm]

def OrderIso.instIsLawfulInfSet (h: β ≃o α) [InfSet β] [InfSet α] [IsLawfulInfSet α]
  (hs: ∀s: Set β, sInf s = h.symm (sInf (s.preimage h.symm))): IsLawfulInfSet β where
  sInf_le := by
    intro s x mem
    have : s.preimage id = s := rfl
    erw [←this, ←funext (g := id) h.coe_symm, ←Set.preimage_preimage]
    apply h.resp_le.mpr
    rw [hs, h.symm_coe]
    apply sInf_le
    apply Set.mem_preimage.mpr
    rw [h.coe_symm, Set.preimage_preimage, Set.preimage_id']
    assumption
    intro
    simp [h.coe_symm]
