import Math.Algebra.Semigroup.Defs

-- we endow Bool with the lattice semiring

instance : Add Bool where
  add := max
instance : Mul Bool where
  mul := min

instance : Zero Bool where
  zero := false
instance : One Bool where
  one := true
instance : NatCast Bool where
  natCast n := n != 0
instance : SMul ℕ Bool where
  smul n x := n * x
instance : Pow Bool ℕ where
  pow x n := n == 0 || x

def Bool.npow_def (x: Bool) (n: ℕ) : x ^ n = ((n == 0) || x) := rfl

instance : IsAddSemigroup Bool where
  add_assoc := by decide
instance : IsSemigroup Bool where
  mul_assoc := by decide
instance : IsAddCommMagma Bool where
  add_comm := by decide
instance : IsCommMagma Bool where
  mul_comm := by decide
instance : IsAddZeroClass Bool where
  add_zero := by decide
  zero_add := by decide
instance : IsMulZeroClass Bool where
  mul_zero := by decide
  zero_mul := by decide
instance : IsMulOneClass Bool where
  mul_one := by decide
  one_mul := by decide
instance : NoZeroDivisors Bool where
  of_mul_eq_zero := by decide
