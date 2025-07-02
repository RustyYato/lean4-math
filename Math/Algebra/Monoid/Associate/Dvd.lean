import Math.Algebra.Dvd.Defs
import Math.Algebra.Monoid.Associate.Defs

variable [MonoidOps α] [Dvd α] [IsMonoid α] [IsLawfulDvd α] [IsCommMagma α] [IsMulCancel α]

def dvd_antisymm (a b: α) : a ∣ b -> b ∣ a -> IsAssociated a b := by
  rw [IsLawfulDvd.dvd_iff, IsLawfulDvd.dvd_iff]
  intro ⟨k₀, h₀⟩ ⟨k₁, h₁⟩
  rw (occs := [1]) [h₁, mul_assoc, ←mul_one b] at h₀
  replace h₀ := mul_left_cancel h₀
  exists ⟨k₀, k₁, ?_, ?_⟩
  symm; rwa [mul_comm]
  symm; assumption
  rw [h₁, mul_assoc]
  dsimp; rw [←h₀, mul_one]

def dvd_of_is_associated (a b: α) : IsAssociated a b -> a ∣ b := by
  rintro ⟨u, rfl⟩
  apply dvd_mul_left
