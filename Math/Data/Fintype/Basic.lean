import Math.Data.Fintype.Fin
import Math.Data.Fintype.Pi
import Math.Data.Fintype.List
import Math.Data.Fintype.Sum
import Math.Data.Fintype.Prod

noncomputable
def Fintype.ofIsFinite (α: Type _) [IsFinite α] : Fintype α :=
  Fintype.ofEquiv (IsFinite.toEquiv α).symm
