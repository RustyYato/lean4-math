import Math.Data.Fintype.Algebra.Monoid
import Math.Algebra.Semiring.Defs

def mul_sum [Fintype ι] [AddMonoidOps α] [Mul α]
  [IsAddMonoid α] [IsAddCommMagma α] [IsLeftDistrib α]
  [IsMulZeroClass α]
  (x: α) (f: ι -> α) : x * ∑i, f i = ∑i, x * f i := by
  let g : α →+ α := {
    toFun a := x * a
    map_zero := by simp
    map_add := by simp [mul_add]
  }
  show g _ = ∑i, g _
  rw [map_sum]

def sum_mul [Fintype ι] [AddMonoidOps α] [Mul α]
  [IsAddMonoid α] [IsAddCommMagma α] [IsRightDistrib α]
  [IsMulZeroClass α]
  (x: α) (f: ι -> α) : (∑i, f i) * x = ∑i, f i * x := by
  let g : α →+ α := {
    toFun a := a * x
    map_zero := by simp
    map_add := by simp [add_mul]
  }
  show g _ = ∑i, g _
  rw [map_sum]
