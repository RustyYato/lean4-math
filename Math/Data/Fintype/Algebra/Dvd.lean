import Math.Algebra.Dvd
import Math.Data.Fintype.Algebra.Monoid

def dvd_prod' [Fintype ι] [One α] [Mul α] [IsSemigroup α] [IsCommMagma α] [Dvd α] [IsLawfulDvd α]
  (i: ι) (f: ι -> α) : f i ∣ ∏i, f i := by
  classical
  have := Fintype.ofEquiv (Equiv.erase i).symm
  rw [prod_eqv (Equiv.erase i).symm, prod_option]
  simp [Equiv.erase]
  rw [dvd_iff]
  exists ∏i: { x // x ≠ i }, f i.val

def dvd_prod [Fintype ι] [One α] [Mul α] [IsSemigroup α] [IsCommMagma α] [Dvd α] [IsLawfulDvd α]
  (a: α) (f: ι -> α) (h: ∃i, a = f i) : a ∣ ∏i, f i := by
  obtain ⟨i, rfl⟩ := h
  apply dvd_prod'
