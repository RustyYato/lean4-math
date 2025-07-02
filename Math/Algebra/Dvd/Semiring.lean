import Math.Algebra.Dvd.Defs
import Math.Algebra.Semiring.Defs

def dvd_add {k a b: α} [Mul α] [AddMonoidOps α] [Dvd α] [IsNonUnitalNonAssocSemiring α] [IsLawfulDvd α] : k ∣ a -> k ∣ b -> k ∣ a + b := by
  rw [dvd_iff, dvd_iff]
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  rw [←mul_add]
  apply dvd_mul_left
