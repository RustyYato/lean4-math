import Math.Algebra.AddMonoidWithOne.Impls.Bool
import Math.Algebra.Semiring.Defs

instance : IsLeftDistrib Bool where
  mul_add := by decide

instance : IsSemiring Bool := IsSemiring.inst
