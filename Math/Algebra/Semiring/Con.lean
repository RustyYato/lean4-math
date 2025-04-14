import Math.Algebra.AddMonoidWithOne.Con
import Math.Algebra.Semiring.Defs

variable {C α: Type*} [RelLike C α] (c: C)

instance [Add α] [Mul α] [IsLeftDistrib α] [IsRingCon C] : IsLeftDistrib (IsCon.Quotient c) where
  mul_add k a b := by
    induction a; induction b; induction k
    apply Quotient.sound
    rw [mul_add]
instance [Add α] [Mul α] [IsRightDistrib α] [IsRingCon C] : IsRightDistrib (IsCon.Quotient c) where
  add_mul a b k := by
    induction a; induction b; induction k
    apply Quotient.sound
    rw [add_mul]

instance [SemiringOps α] [IsSemiring α] [IsRingCon C] : IsSemiring (IsCon.Quotient c) := IsSemiring.inst

def IsRingCon.mkQuot [SemiringOps α] [IsSemiring α] [IsRingCon C] : α →+* IsCon.Quotient c where
  toFun a := IsCon.mkQuot c a
  map_zero := rfl
  map_one := rfl
  map_add := rfl
  map_mul := rfl

def RingCon.mkQuot_kernel [SemiringOps α] [IsSemiring α] (c: RingCon α) : RingCon.kernel (IsRingCon.mkQuot c) = c := by
  apply le_antisymm
  · intro x y h
    exact Quotient.exact h
  · intro x y h
    exact Quotient.sound h
