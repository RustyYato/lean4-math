import Math.Algebra.Monoid.Order.Defs
import Math.Order.Lattice.Basic

class Dist (α: Type*) (β: outParam Type*) where
  dist: α -> α -> β

export Dist (dist)

class IsPseudoMetricSpace (α: Type*) {β: outParam Type*}
  [LT β] [LE β] [AddMonoidOps β] [IsOrderedAddCommMonoid β]
  [Dist α β] : Prop extends IsLinearOrder β where
  dist_self: ∀x: α, dist x x = 0
  dist_comm: ∀x y: α, dist x y = dist y x
  dist_triangle: ∀x y k: α, dist x y ≤ dist x k + dist k y

class IsMetricSpace (α: Type α) {β: outParam Type*}
  [LT β] [LE β] [Zero β] [Add β] [SMul ℕ β]
  [IsOrderedAddCommMonoid β]
  [Dist α β] : Prop extends IsPseudoMetricSpace α where
  of_dist_eq_zero: ∀x y: α, dist x y = 0 -> x = y

section

variable [LT β] [LE β] [AddMonoidOps β] [IsOrderedAddCommMonoid β]
  [Dist α β] [IsPseudoMetricSpace α]

def dist_self: ∀x: α, dist x x = 0 := IsPseudoMetricSpace.dist_self
def dist_comm: ∀x y: α, dist x y = dist y x := IsPseudoMetricSpace.dist_comm
def dist_triangle: ∀x y k: α, dist x y ≤ dist x k + dist k y := IsPseudoMetricSpace.dist_triangle

end

section

variable [LT β] [LE β] [AddMonoidOps β] [IsOrderedAddCommMonoid β]
  [Dist α β] [IsMetricSpace α]

def of_dist_eq_zero: ∀x y: α, dist x y = 0 -> x = y := IsMetricSpace.of_dist_eq_zero

end

def dist_nonneg
  [LT β] [LE β] [Zero β] [Add β] [SMul ℕ β]
  [IsOrderedAddCommMonoid β] [IsAddCancel β]
  [Dist α β] [IsPseudoMetricSpace α] (a b: α) : 0 ≤ dist a b := by
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
  [Dist α β] [IsMetricSpace α] (a b: α) (h: a ≠ b) : 0 < dist a b := by
  apply lt_of_le_of_ne
  apply dist_nonneg
  intro g
  have := of_dist_eq_zero _ _ g.symm
  contradiction

instance
  Prod.distSup [Dist α γ] [Dist β γ] [Sup γ] : Dist (α × β) γ where
  dist x y := dist x.fst y.fst ⊔ dist x.snd y.snd

instance
  Prod.psuedometricSpaceSup
  [Dist α γ] [Dist β γ]
  [LE γ] [LT γ] [AddMonoidOps γ]
  [IsOrderedAddCommMonoid γ]
  [Sup γ] [IsSemiLatticeSup γ]
  [IsAddCancel γ]
  [IsPseudoMetricSpace α] [IsPseudoMetricSpace β] : IsPseudoMetricSpace (α × β) where
  dist_self := by
    intro x
    show _ ⊔ _ = _
    rw [dist_self, dist_self, sup_self]
  dist_comm := by
    intro a b
    show dist _ _ ⊔ dist _ _ = dist _ _ ⊔ dist _ _
    congr 1 <;> apply dist_comm
  dist_triangle := by
    intro a b k
    show dist _ _ ⊔ dist _ _ ≤ (dist _ _ ⊔ dist _ _) + (dist _ _ ⊔ dist _ _)
    rw [sup_le_iff]; apply And.intro
    apply flip le_trans
    apply add_le_add
    apply le_sup_left
    apply le_sup_left
    apply dist_triangle
    apply flip le_trans
    apply add_le_add
    apply le_sup_right
    apply le_sup_right
    apply dist_triangle

instance
  Prod.metricSpaceSup
  [Dist α γ] [Dist β γ]
  [LE γ] [LT γ] [AddMonoidOps γ]
  [IsOrderedAddCommMonoid γ]
  [Sup γ] [IsSemiLatticeSup γ]
  [IsAddCancel γ]
  [IsMetricSpace α] [IsMetricSpace β] : IsMetricSpace (α × β) where
  of_dist_eq_zero a b h := by
    replace h: _ ⊔ _ = (0: γ) := h
    by_cases h₀:dist a.fst b.fst ≤ 0
    replace h₀ := of_dist_eq_zero _ _ <| le_antisymm h₀ (dist_nonneg _ _ )
    rw [h₀, dist_self, sup_eq_right.mpr] at h
    ext
    assumption
    exact of_dist_eq_zero _ _ h
    apply dist_nonneg
    rw [not_le] at h₀
    have h₁ : 0 < dist a.fst b.fst ⊔ dist a.snd b.snd := by
      apply lt_sup_left
      assumption
    rw [h] at h₁
    have := lt_irrefl h₁
    contradiction

variable
  [Dist α γ] [Dist β γ]
  [LE γ] [LT γ] [AddMonoidOps γ]
  [IsOrderedAddCommMonoid γ]
  [Sup γ] [IsSemiLatticeSup γ]
  [IsAddCancel γ]
  [IsMetricSpace α] [IsMetricSpace β]

instance : IsMetricSpace (α × β) := Prod.metricSpaceSup

#synth IsMetricSpace (α × β)
