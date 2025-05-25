import Math.Data.Fintype.Algebra.Monoid
import Math.Algebra.Monoid.Action.Defs

def smul_sum
  [Fintype ι]
  [MonoidOps γ] [IsMonoid γ]
  [AddMonoidOps α] [IsAddMonoid α] [IsAddCommMagma α]
  [SMul γ α] [IsDistribMulAction γ α]
  (x: γ) (f: ι -> α) : x • ∑i, f i = ∑i, x • f i := by
  let g : α →+ α := {
    toFun a := x • a
    map_zero := by simp
    map_add := by simp [smul_add]
  }
  show g _ = ∑i, g _
  rw [map_sum]
