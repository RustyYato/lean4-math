import Math.Data.Finset.Basic
import Math.Data.LazyFinset.Defs

namespace Equiv

def lazy_finset_eqv_finset [DecidableEq α] : LazyFinset α ≃ Finset α where
  toFun s := {
    val := s.toMultiset
    property := LazyFinset.toMultiset_nodup _
  }
  invFun s := LazyFinset.ofMultiset s.val
  leftInv s := by simp
  rightInv s := by
    ext x
    show x ∈ LazyFinset.toMultiset (LazyFinset.ofMultiset s.val) ↔ _
    simp
    rfl

end Equiv
