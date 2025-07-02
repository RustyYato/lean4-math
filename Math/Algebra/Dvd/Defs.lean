import Math.Algebra.Monoid.Units.Defs

class IsLawfulDvd (α: Type*) [Dvd α] [Mul α]: Prop where
  dvd_iff {a b: α} : (a ∣ b) ↔ ∃k, b = a * k := by intros; rfl

def dvd_iff [Dvd α] [Mul α] [IsLawfulDvd α] {a b: α} : (a ∣ b) ↔  ∃k, b = a * k := IsLawfulDvd.dvd_iff

instance : IsLawfulDvd Nat where
instance : IsLawfulDvd Int where

namespace IsLawfulDvd.ofMul

variable [Mul α]

scoped instance : Dvd α where
  dvd a b := ∃k, b = a * k

scoped instance : IsLawfulDvd α where
  dvd_iff := Iff.rfl

end IsLawfulDvd.ofMul

variable {α: Type*} [Dvd α]

section

variable [MonoidOps α] [IsMonoid α] [IsLawfulDvd α]

def unit_dvd (a b: α) [IsUnit a] : a ∣ b := by
  rw [dvd_iff]
  exists IsUnit.inv a * b
  rw [←mul_assoc, IsUnit.mul_inv, one_mul]

def one_dvd (a: α) : 1 ∣ a := by
  apply unit_dvd

@[refl]
def dvd_refl (a: α) : a ∣ a := dvd_iff.mpr ⟨1, (mul_one _).symm⟩

def of_dvd_unit (a b: α) [IsUnit b] [IsCommMagma α] : a ∣ b -> IsUnit a := by
  rw [dvd_iff]
  intro ⟨a', _⟩
  subst b
  apply IsUnit.mk
  refine ⟨⟨a, a' * IsUnit.inv (a * a'), ?_, ?_⟩, rfl⟩
  rw [←mul_assoc, IsUnit.mul_inv]
  rw [mul_comm a', mul_assoc, mul_comm a', IsUnit.inv_mul]

end

def dvd_mul_left [Mul α] [IsLawfulDvd α] (a b: α) : a ∣ a * b := by
  rw [dvd_iff]
  exists b

def dvd_mul_right [Mul α] [IsCommMagma α] [IsLawfulDvd α] (a b: α) : a ∣ b * a := by
  rw [mul_comm]
  apply dvd_mul_left

def dvd_trans {a b c: α} [Mul α] [IsSemigroup α] [IsLawfulDvd α] : a ∣ b -> b ∣ c -> a ∣ c := by
  rw [dvd_iff, dvd_iff, dvd_iff]
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩
  exists a * b
  rw [mul_assoc]

def dvd_absorb [Mul α] [IsLawfulDvd α] (a b: α) (h: IsAbsorbing b) : a ∣ b := by
  rw [dvd_iff]
  exists b
  rw [IsAbsorbing.mul_left]

def dvd_zero [Mul α] [Zero α] [IsMulZeroClass α] [IsLawfulDvd α] (a: α) : a ∣ 0 := by
  apply dvd_absorb
  infer_instance
