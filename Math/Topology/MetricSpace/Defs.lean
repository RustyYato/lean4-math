import Math.Algebra.Monoid.Order.Defs
import Math.Order.Lattice.Basic

class Dist (α: Type*) (β: outParam Type*) where
  dist: α -> α -> β

export Dist (dist)

class IsPseudoMetric (α: Type*) {β: Type*}
  [LT β] [LE β] [AddMonoidOps β] [IsOrderedAddCommMonoid β]
  [Dist α β] [IsLinearOrder β] : Prop where
  dist_self: ∀x: α, dist x x = 0
  dist_comm: ∀x y: α, dist x y = dist y x
  dist_triangle: ∀x y k: α, dist x y ≤ dist x k + dist k y

class IsMetric (α: Type α) {β: Type*}
  [LT β] [LE β] [Zero β] [Add β] [SMul ℕ β]
  [IsOrderedAddCommMonoid β] [IsLinearOrder β]
  [Dist α β] : Prop extends IsPseudoMetric α where
  of_dist_eq_zero: ∀x y: α, dist x y = 0 -> x = y

section

variable [LT β] [LE β] [AddMonoidOps β] [IsOrderedAddCommMonoid β]
  [IsLinearOrder β] [Dist α β] [IsPseudoMetric α]

def dist_self: ∀x: α, dist x x = 0 := IsPseudoMetric.dist_self
def dist_comm: ∀x y: α, dist x y = dist y x := IsPseudoMetric.dist_comm
def dist_triangle: ∀x y k: α, dist x y ≤ dist x k + dist k y := IsPseudoMetric.dist_triangle

end

section

variable [LT β] [LE β] [AddMonoidOps β] [IsOrderedAddCommMonoid β]
  [IsLinearOrder β] [Dist α β] [IsMetric α]

def of_dist_eq_zero: ∀x y: α, dist x y = 0 -> x = y := IsMetric.of_dist_eq_zero

end

def dist_nonneg
  [LT β] [LE β] [Zero β] [Add β] [SMul ℕ β]
  [IsOrderedAddCommMonoid β] [IsAddCancel β]
  [Dist α β] [IsLinearOrder β] [IsPseudoMetric α] (a b: α) : 0 ≤ dist a b := by
  have : 0 ≤ 2 • dist a b := by
    rw [nsmul_eq_nsmulRec, nsmulRec, nsmulRec, nsmulRec, zero_add]
    conv => {
      rhs; lhs; rw [dist_comm]
    }
    rw [←dist_self b]
    apply dist_triangle
  rw [←nsmul_zero] at this
  apply le_of_nsmul_le_nsmul _ _ _ _ this
  exact Nat.zero_lt_two

def dist_pos {β α}
  [LT β] [LE β] [Zero β] [Add β] [SMul ℕ β]
  [IsOrderedAddCommMonoid β] [IsAddCancel β]
  [Dist α β] [IsLinearOrder β] [IsMetric α] (a b: α) (h: a ≠ b) : 0 < dist a b := by
  apply lt_of_le_of_ne
  apply dist_nonneg
  intro g
  have := of_dist_eq_zero _ _ g.symm
  contradiction

instance
  Prod.distMax [Dist α γ] [Dist β γ] [Max γ] : Dist (α × β) γ where
  dist x y := max (dist x.fst y.fst) (dist x.snd y.snd)

instance
  Prod.psuedometricMax
  [Dist α γ] [Dist β γ]
  [LE γ] [LT γ] [AddMonoidOps γ]
  [IsOrderedAddCommMonoid γ]
  [Min γ] [Max γ] [IsLinearLattice γ]
  [IsPseudoMetric α] [IsPseudoMetric β] : IsPseudoMetric (α × β) where
  dist_self := by
    intro x
    show max _ _ = _
    rw [dist_self, dist_self, max_eq_right.mpr (le_refl _)]
  dist_comm := by
    intro a b
    show max (dist _ _) (dist _ _) = max (dist _ _) (dist _ _)
    congr 1 <;> apply dist_comm
  dist_triangle := by
    intro a b k
    show max (dist _ _) (dist _ _) ≤ max (dist _ _) (dist _ _) + max (dist _ _) (dist _ _)
    rw [max_le_iff]; apply And.intro
    apply flip le_trans
    apply add_le_add
    apply le_max_left
    apply le_max_left
    apply dist_triangle
    apply flip le_trans
    apply add_le_add
    apply le_max_right
    apply le_max_right
    apply dist_triangle

open Classical in
instance
  Prod.metricMax
  [Dist α γ] [Dist β γ]
  [LE γ] [LT γ] [AddMonoidOps γ]
  [IsAddCancel γ] [IsOrderedAddCommMonoid γ]
  [Min γ] [Max γ] [IsLinearLattice γ]
  [IsMetric α] [IsMetric β] : IsMetric (α × β) where
  of_dist_eq_zero a b h := by
    replace h: max _ _ = (0: γ) := h
    by_cases h₀:dist a.fst b.fst ≤ 0
    replace h₀ := of_dist_eq_zero _ _ <| le_antisymm h₀ (dist_nonneg _ _ )
    rw [h₀, dist_self, max_def] at h
    ext
    assumption
    split at h <;> rename_i g
    exact of_dist_eq_zero _ _ h
    exfalso; apply g
    apply dist_nonneg
    exfalso; apply h₀
    apply le_of_le_of_eq _ h
    apply le_max_left
