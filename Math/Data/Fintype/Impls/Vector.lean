import Math.Data.Fintype.Impls.Pi
import Math.Data.ListVector.Basic

instance [Fintype α] : Fintype (List.Vector α n) :=
  Fintype.ofEquiv (List.Vector.equivFinFunc _ _)
