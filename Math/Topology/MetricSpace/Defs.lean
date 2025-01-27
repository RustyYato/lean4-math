import Math.Order.Linear
import Math.Algebra.Order

class Dist (α: Type*) (β: outParam Type*) where
  dist: α -> α -> β

export Dist (dist)

class IsPseudoMetricSpace (α: Type*) {β: outParam Type*}
  [LT β] [LE β] [Zero β] [Add β] [SMul ℕ β]
  [IsOrderedAddCommMonoid β]
  [Dist α β] extends IsPreOrder β: Prop where
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

instance [Add γ] [Dist α γ] [Dist β γ] : Dist (α × β) γ where
  dist x y := dist x.fst y.fst + dist x.snd y.snd

def dist_nonneg
  [LT β] [LE β] [Zero β] [Add β] [SMul ℕ β]
  [IsOrderedAddCommMonoid β]
  [Dist α β] [IsPseudoMetricSpace α] (a b: α) : 0 ≤ dist a b := by
  have : 0 ≤ 2 • dist a b := by
    rw [nsmul_eq_nsmulRec, nsmulRec, nsmulRec, nsmulRec, zero_add]
    conv => {
      rhs; lhs; rw [dist_comm]
    }
    rw [←dist_self b]
    apply dist_triangle
  rw [←nsmul_zero] at this
  refine (le_iff_nsmul_le _ _ _ ?_).mpr this
  decide

instance
  [Dist α γ] [Dist β γ]
  [LE γ] [LT γ] [Zero γ] [Add γ] [SMul ℕ γ]
  [IsOrderedAddCommMonoid γ]
  [IsPseudoMetricSpace α] [IsPseudoMetricSpace β] : IsPseudoMetricSpace (α × β) where
  dist_self := by
    intro x
    show _ + _ = _
    rw [dist_self, dist_self, add_zero]
  dist_comm := by
    intro a b
    show dist _ _ + dist _ _ = dist _ _ + dist _ _
    congr 1 <;> apply dist_comm
  dist_triangle := by
    intro a b k
    show dist _ _ + dist _ _ ≤ (dist _ _ + dist _ _) + (dist _ _ + dist _ _)
    rw [add_assoc, ←add_assoc (dist a.snd _),
      add_comm (dist a.snd _), add_assoc, ←add_assoc]
    apply add_le_add
    apply dist_triangle
    apply dist_triangle

instance
  [Dist α γ] [Dist β γ]
  [LE γ] [LT γ] [Zero γ] [Add γ] [SMul ℕ γ] [IsAddCancel γ]
  [IsOrderedAddCommMonoid γ]
  [IsMetricSpace α] [IsMetricSpace β] : IsMetricSpace (α × β) where
  of_dist_eq_zero a b h := by
    replace h: _ + _ = (0: γ) := h
    by_cases h₀:dist a.fst b.fst ≤ 0
    replace h₀ := of_dist_eq_zero _ _ <| le_antisymm h₀ (dist_nonneg _ _ )
    rw [h₀, dist_self, zero_add] at h
    ext
    assumption
    exact of_dist_eq_zero _ _ h
    by_cases h₁:dist a.snd b.snd ≤ 0
    replace h₁ := of_dist_eq_zero _ _ <| le_antisymm h₁ (dist_nonneg _ _ )
    rw [h₁, dist_self, add_zero] at h
    rw [h] at h₀; have := h₀ (le_refl _)
    contradiction
    replace h₀ := lt_of_le_of_not_le (dist_nonneg _ _) h₀
    replace h₁ := lt_of_le_of_not_le (dist_nonneg _ _) h₁
    have := add_lt_add _ _ _ _ h₀ h₁
    rw [zero_add] at this
    rw [h] at this
    have := lt_irrefl this
    contradiction

export IsMetricSpace (of_dist_eq_zero)
