import Math.Algebra.Semidomain.Defs
import Math.Algebra.Hom.Defs
import Math.Algebra.Monoid.Associate.Defs
import Math.Algebra.Group.Units.Defs

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

def apply_normUnit (a: α) : normUnit a = NormalizationMonoid.normUnit a := rfl

def normalize : α →* α where
  toFun a := a * (normUnit a: α)
  map_one := by rw [map_one, one_mul]; rfl
  map_mul {x y} := by rw [map_mul, Units.val_mul, mul_assoc, mul_left_comm y, ←mul_assoc x]

@[simp] def apply_normalize (a: α) : normalize a = a * normUnit a := rfl

def normalize₀ [Zero α] [IsMulZeroClass α] : α →*₀ α := {
  normalize with
  map_zero := by
    show (0: α) * NormalizationMonoid.normUnit (0: α) = 0
    rw [zero_mul]
}

@[simp] def apply_normalize₀ [Zero α] [IsMulZeroClass α] (a: α) : normalize₀ a = a * normUnit a := rfl

def normalize_unit (a: Units α) : normalize a.val = 1 := by
  simp [apply_normalize, apply_normUnit, NormalizationMonoid.normUnit_unit a, ←Units.val_mul]

def normalize_isassoc (a: α) : IsAssociates (normalize a) a := by
  exists (normUnit a)⁻¹
  simp [mul_assoc, ←Units.val_mul]

def normalize_eq_of_isassoc (a b: α) (h: IsAssociates a b) : normalize a = normalize b := by
  obtain ⟨u, rfl⟩ := h
  rw [map_mul, normalize_unit, mul_one]

protected def Associates.normalize : Associates α →* α := by
  refine (Associates.Con α).liftGroupHom normalize ?_
  intro a b h
  apply normalize_eq_of_isassoc
  assumption

protected def Associates.normalize₀ [Zero α] [IsMulZeroClass α] : Associates α →*₀ α := by
  refine (Associates.Con α).liftGroupWithZeroHom normalize₀ ?_
  intro a b h
  apply normalize_eq_of_isassoc
  assumption

def Associates.apply_mk_normalize (a: α) : (Associates.mk a).normalize = normalize a := rfl
def Associates.apply_mk_normalize₀ [Zero α] [IsMulZeroClass α] (a: α) : (Associates.mk a).normalize₀ = normalize₀ a := rfl

end
