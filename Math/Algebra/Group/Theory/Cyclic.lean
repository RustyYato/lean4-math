import Math.Algebra.Group.Theory.Basic
import Math.Algebra.Impls.Fin

-- the cyclic group of order n
instance Cyclic (n: ℕ) [h: NeZero n] : Group (Fin n) := by
  match n, h with
  | n + 1, h =>
  apply Group.ofAdd
