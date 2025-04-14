import Math.Order.TopBot
import Math.Data.Set.Order.Bounds
import Math.Order.OrderIso.Set

namespace OrderEquiv

def instSupSet [SupSet α] [LE α] [LE β] (h: β ≃o α) : SupSet β where
  sSup s := h.symm (⨆ (s.preimage h.symm))

def instInfSet [InfSet α] [LE α] [LE β] (h: β ≃o α) : InfSet β where
  sInf s := h.symm (⨅ (s.preimage h.symm))

end OrderEquiv

noncomputable section

open Classical

instance instSupSetWithTop [SupSet α] [LE α] : SupSet (WithTop α) where
  sSup s :=
    have s' := s.preimage .of
    if ⊤ ∈ s ∨ ¬Set.BoundedAbove s' then ⊤
    else ↑(⨆ (s.preimage .of))

instance instInfSetWithTop [InfSet α] [LE α] : InfSet (WithTop α) where
  sInf s :=
    if s ⊆ {⊤} ∨ ¬s.BoundedBelow then ⊤
    else ↑(⨅ (s.preimage .of))

instance instSupSetWithBot [SupSet α] [LE α] : SupSet (WithBot α) :=
  WithBot.orderIsoWithTop.instSupSet
instance instInfSetWithBot [InfSet α] [LE α] : InfSet (WithBot α) :=
  WithBot.orderIsoWithTop.instInfSet

private
def WithBot.sSup_def [SupSet α] [_root_.LE α] (s: Set (WithBot α)) : ⨆ s = (
  WithBot.orderIsoWithTop.symm (⨆ (s.preimage WithBot.orderIsoWithTop.symm))
) := rfl

instance [SupSet α] [LE α] [IsLawfulSupSet α] : IsLawfulSupSet (WithTop α) where
  le_sSup := by
    intro s x mem
    simp [sSup]
    cases x
    rw [if_pos (.inl mem)]
    apply WithTop.LE.top
    split
    apply WithTop.LE.top
    apply WithTop.LE.of
    apply le_sSup
    assumption

instance [InfSet α] [LE α] [IsLawfulInfSet α] : IsLawfulInfSet (WithTop α) where
  sInf_le := by
    intro s x mem
    simp [sInf]
    split <;> rename_i h
    rcases h with h | h
    cases Set.mem_singleton.mp <| h _ mem
    apply le_top
    · cases x
      apply le_top
      rename_i x
      exfalso
      apply h
      exists ↑(⨅ (s.preimage WithTop.of))
      intro y hy
      cases y
      apply le_top
      apply WithTop.LE.of
      apply sInf_le (α := α) (s := s.preimage WithTop.of) hy
    cases x
    apply WithTop.LE.top
    apply WithTop.LE.of
    apply sInf_le
    exact mem

instance [InfSet α] [LE α] [IsLawfulInfSet α] : IsLawfulInfSet (WithBot α) :=
  WithBot.orderIsoWithTop.instIsLawfulInfSet fun _ => rfl

instance [SupSet α] [LE α] [IsLawfulSupSet α] : IsLawfulSupSet (WithBot α) :=
  WithBot.orderIsoWithTop.instIsLawfulSupSet <| fun _ => rfl

end
