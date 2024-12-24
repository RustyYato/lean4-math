import Math.Data.Fintype.Fin
import Math.Data.Fintype.Pi
import Math.Data.Fintype.List
import Math.Data.Fintype.Sum
import Math.Data.Fintype.Prod
import Math.Data.Fintype.Subtype

noncomputable
def Fintype.ofIsFinite (α: Type _) [IsFinite α] : Fintype α :=
  Fintype.ofEquiv (IsFinite.toEquiv α).symm

instance : Fintype UInt8 := Fintype.ofEquiv UInt8.equivFin.symm
instance : Fintype UInt16 := Fintype.ofEquiv UInt16.equivFin.symm
instance : Fintype UInt32 := Fintype.ofEquiv UInt32.equivFin.symm
instance : Fintype UInt64 := Fintype.ofEquiv UInt64.equivFin.symm
instance : Fintype Char := Fintype.ofEquiv Char.equivSubtype.symm
