import Math.Order.OrderIso
import Math.Order.Lattice.Complete

variable [Max α] [Min α] [SupSet α] [InfSet α] [LE α] [LT α] [Top α] [Bot α]
variable [IsCompleteLattice α] (f : α →≤ α)

namespace MonotoneHom

/-- Least fixed point of a monotone function -/
def lfp : (α →≤ α) →≤ α where
  toFun f := ⨅ (Set.mk fun a => f a ≤ a)
  monotone _ _ hle := sInf_le_sInf fun a ha => le_trans (hle a) ha

/-- Greatest fixed point of a monotone function -/
def gfp : (α →≤ α) →≤ α where
  toFun f := ⨆ (Set.mk fun a => a ≤ f a)
  monotone _ _ hle := sSup_le_sSup fun a ha => le_trans ha (hle a)

def lfp_le {a : α} (h : f a ≤ a) : lfp f ≤ a :=
  sInf_le h

def lfp_le_fixed {a : α} (h : f a = a) : lfp f ≤ a :=
  f.lfp_le (le_of_eq h)

def le_lfp {a : α} (h : ∀ b, f b ≤ b → a ≤ b) : a ≤ lfp f :=
  le_sInf _ _ h

def resp_le_lfp {a : α} (ha : a ≤ lfp f) : f a ≤ lfp f :=
  f.le_lfp fun _ hb => le_trans (f.monotone <| le_sInf_iff.mp ha _ hb) hb

def map_lfp : f (lfp f) = lfp f :=
  have h : f (lfp f) ≤ lfp f := f.resp_le_lfp (le_refl _)
  le_antisymm h <| f.lfp_le <| f.monotone h

end MonotoneHom
