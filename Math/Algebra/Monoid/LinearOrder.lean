import Math.Algebra.Monoid.Order

variable [LT α] [LE α] [LT β] [LE β] [IsLinearOrder α]

variable  [MonoidOps α] [IsOrderedCommMonoid α]

def le_of_nsmul_le_nsmul (a b: α) (n: ℕ) (h: 0 < n) :
  n • a ≤ n • b -> a ≤ b := by
  cases n with
  | zero => contradiction
  | succ n =>
  clear h; intro h
  rw [succ_nsmul, succ_nsmul] at h
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [succ_nsmul, succ_nsmul] at h
    sorry
