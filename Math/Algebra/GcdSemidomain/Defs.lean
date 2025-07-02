import Math.Algebra.Semidomain.Defs
import Math.Algebra.Hom.Defs

section

class NormalizationMonoid (α: Type*) [MonoidOps α] [IsMonoid α] [IsCommMagma α] where
  protected normUnit: α -> Units α
  normUnit_mul (a b: α) : normUnit (a * b) = normUnit a * normUnit b
  normUnit_unit (a: Units α) : normUnit a.val = a⁻¹
  -- all absorbing elements get mapped to one
  normUnit_absorbing (x: α) (h: ∀a: α, x * a = x) : normUnit x = 1

variable [MonoidOps α] [IsMonoid α] [IsCommMagma α] [NormalizationMonoid α]

def normUnit : α →* Units α where
  toFun a := NormalizationMonoid.normUnit a
  map_one := NormalizationMonoid.normUnit_unit 1
  map_mul := NormalizationMonoid.normUnit_mul _ _

def normalize : α →* α where
  toFun a := a * (normUnit a: α)
  map_one := by rw [map_one, one_mul]; rfl
  map_mul {x y} := by rw [map_mul, Units.val_mul, mul_assoc, mul_left_comm y, ←mul_assoc x]

def normalize₀ [Zero α] [IsMulZeroClass α] : α →*₀ α := {
  normalize with
  map_zero := by
    show (0: α) * NormalizationMonoid.normUnit (0: α) = 0
    rw [zero_mul]
}

end
