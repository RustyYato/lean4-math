import Math.Order.OrderIso
import Math.Order.Lattice.Complete

variable [Sup α] [Inf α] [SupSet α] [InfSet α] [LE α] [LT α] [Top α] [Bot α]
variable [IsCompleteLattice α] (f : α →o α)

namespace OrderHom

/-- Least fixed point of a monotone function -/
def lfp : (α →o α) →o α where
  toFun f := sInf (Set.mk fun a => f a ≤ a)
  resp_rel hle := sInf_le_sInf fun a ha => le_trans (hle a) ha

/-- Greatest fixed point of a monotone function -/
def gfp : (α →o α) →o α where
  toFun f := sSup (Set.mk fun a => a ≤ f a)
  resp_rel hle := sSup_le_sSup fun a ha => le_trans ha (hle a)

def lfp_le {a : α} (h : f a ≤ a) : lfp f ≤ a :=
  sInf_le h

def lfp_le_fixed {a : α} (h : f a = a) : lfp f ≤ a :=
  f.lfp_le (le_of_eq h)

def le_lfp {a : α} (h : ∀ b, f b ≤ b → a ≤ b) : a ≤ lfp f :=
  le_sInf _ _ h

def resp_le_lfp {a : α} (ha : a ≤ lfp f) : f a ≤ lfp f :=
  f.le_lfp fun _ hb => le_trans (f.resp_rel <| le_sInf_iff.mp ha _ hb) hb

def map_lfp : f (lfp f) = lfp f :=
  have h : f (lfp f) ≤ lfp f := f.resp_le_lfp (le_refl _)
  le_antisymm h <| f.lfp_le <| f.resp_rel h

end OrderHom
