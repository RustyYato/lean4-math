import Math.Data.Fintype.Fin
import Math.Data.Fintype.Pi
import Math.Data.Fintype.List
import Math.Data.Fintype.Sum
import Math.Data.Fintype.Prod
import Math.Data.Fintype.Subtype
import Math.Data.Fintype.Option

noncomputable
def Fintype.ofIsFinite (α: Type _) [IsFinite α] : Fintype α :=
  Fintype.ofEquiv (IsFinite.toEquiv α).symm

instance : Fintype UInt8 := Fintype.ofEquiv UInt8.equivFin.symm
instance : Fintype UInt16 := Fintype.ofEquiv UInt16.equivFin.symm
instance : Fintype UInt32 := Fintype.ofEquiv UInt32.equivFin.symm
instance : Fintype UInt64 := Fintype.ofEquiv UInt64.equivFin.symm
instance : Fintype Char := Fintype.ofEquiv Char.equivSubtype.symm
instance : Fintype Bool where
  all := [false, true]
  nodup := by decide
  complete := by decide

instance [Inhabited α] [Subsingleton α] : Fintype α where
  all := [default]
  nodup := List.Pairwise.cons nofun List.Pairwise.nil
  complete x := Subsingleton.allEq x default ▸ List.Mem.head _

instance [IsEmpty α] : Fintype α where
  all := []
  nodup := List.Pairwise.nil
  complete a := (elim_empty a).elim
