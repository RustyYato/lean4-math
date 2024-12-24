import Math.Data.Fintype.Fin

noncomputable
def Fintype.ofIsFinite (α: Type _) [IsFinite α] : Fintype α :=
  Fintype.ofEquiv (IsFinite.toEquiv α).symm
