import Math.Order.Linear
import Math.Algebra.Order

class Dist (α: Type*) (β: outParam Type*) where
  dist: α -> α -> β

export Dist (dist)

class IsPseudoMetricSpace (α: Type*) {β: outParam Type*}
  [LT β] [LE β] [Zero β] [Add β] [SMul ℕ β]
  [IsOrderedAddCommMonoid β]
  [Dist α β] extends IsLinearOrder β: Prop where
  dist_self: ∀x: α, dist x x = 0
  dist_comm: ∀x y: α, dist x y = dist y x
  dist_triangle: ∀x y k: α, dist x y ≤ dist x k + dist k y

export IsPseudoMetricSpace (dist_self dist_comm dist_triangle)

class IsMetricSpace (α: Type α) {β: outParam Type*}
  [LT β] [LE β] [Zero β] [Add β] [SMul ℕ β]
  [IsOrderedAddCommMonoid β]
  [Dist α β] extends IsPseudoMetricSpace α: Prop where
  of_dist_eq_zero: ∀x y: α, dist x y = 0 -> x = y

export IsMetricSpace (of_dist_eq_zero)
