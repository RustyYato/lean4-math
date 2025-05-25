import Math.Data.«Fintype-old».Defs

-- the elements of a finset is a finite type
instance (f: Finset α) : Fintype f where
  all := f.attach
  complete := Finset.mem_attach _

instance [f: Fintype α] : Fintype (Finset α) where
  all := (Finset.univ α).powerset
  complete := by
    intro x
    rw [Finset.mem_powerset]
    intro _ _
    apply Finset.mem_univ
