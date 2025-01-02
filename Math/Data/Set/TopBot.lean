import Math.Data.Set.Basic
import Math.Order.TopBot
import Math.Data.Set.Order.Bounds

namespace OrderIso

def instSupSet [SupSet α] [LE α] [LE β] (h: β ≃o α) : SupSet β where
  sSup s := h.symm (sSup (s.preimage h.symm))

def instInfSet [InfSet α] [LE α] [LE β] (h: β ≃o α) : InfSet β where
  sInf s := h.symm (sInf (s.preimage h.symm))

end OrderIso

noncomputable section

open Classical

instance instSupSetWithTop [SupSet α] [LE α] : SupSet (WithTop α) where
  sSup s :=
    have s' := s.preimage .of
    if ⊤ ∈ s ∨ ¬Set.BoundedAbove s' then ⊤
    else ↑(sSup (s.preimage .of))

instance instInfSetWithTop [InfSet α] [LE α] : InfSet (WithTop α) where
  sInf s :=
    if s ⊆ {⊤} ∨ ¬s.BoundedBelow then ⊤
    else ↑(sInf (s.preimage .of))

instance instSupSetWithBot [SupSet α] [LE α] : SupSet (WithBot α) :=
  WithBot.orderIsoWithTop.instSupSet
instance instInfSetWithBot [InfSet α] [LE α] : InfSet (WithBot α) :=
  WithBot.orderIsoWithTop.instInfSet

end
