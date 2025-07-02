import Math.Algebra.Dvd.Semiring
import Math.Algebra.Ring.Defs

def dvd_neg [RingOps α] [Dvd α] [IsRing α] [IsLawfulDvd α] {a b: α} : a ∣ b ↔ a ∣ -b := by
  rw [dvd_iff, dvd_iff]
  apply Iff.intro
  rintro ⟨k, rfl⟩
  exists -k
  rw [←mul_neg]
  intro ⟨k, eq⟩
  exists -k
  rw [mul_neg, ←eq, neg_neg]
