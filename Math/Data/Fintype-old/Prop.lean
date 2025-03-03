import Math.Data.Fintype.Defs

instance : Fintype Prop where
  all := [False, True]
  nodup := by simp
  complete := by
    intro x
    simp; symm
    apply Classical.em
