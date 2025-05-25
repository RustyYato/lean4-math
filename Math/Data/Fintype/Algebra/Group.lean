import Math.Data.Fintype.Algebra.Monoid
import Math.Algebra.Group.Defs

variable [Fintype ι] [AddGroupOps α] [IsAddGroup α] [IsAddCommMagma α]

def neg_sum (f: ι -> α) : -∑i, f i = ∑i, -f i := by
  let g : α →+ α := {
    toFun a := -a
    map_zero := by simp
    map_add := by simp [neg_add_rev, add_comm]
  }
  show g _ = ∑i, g _
  rw [map_sum]

def sum_sub_sum (f g: ι -> α) : (∑i, f i) - (∑i, g i) = ∑i, f i - g i := by
  simp [sub_eq_add_neg, neg_sum, sum_pairwise]
