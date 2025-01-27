import Math.Order.Linear
import Math.Function.Basic
import Math.Ops.Abs
import Math.Topology.MetricSpace.Defs
import Math.Relation.Basic

namespace CauchySeq

variable {α: Type*} [Dist α γ] [LT γ] [LE γ] [Zero γ]
  [Add α] [Add γ] [Zero α] [Zero γ] [SMul ℕ α] [SMul ℕ γ]
  [SMul ℤ α] [Sub α] [Neg α] [IsAddGroup α]
  [IsAddMonoid α] [IsAddCommMagma α]
  [One γ] [IsNontrivial γ] [Mul γ] [Pow γ ℕ] [NatCast γ] [∀n, OfNat γ (n + 2)]
  [IsOrderedSemiring γ]
  [Min γ] [Max γ] [IsAddCancel γ]
  [IsLinearMinMaxOrder γ] [IsMetricSpace α]
  [Sub γ] [Pow γ ℤ] [SMul ℤ γ] [Neg γ] [IntCast γ] [CheckedInvert γ (· ≠ 0)] [CheckedDiv γ (· ≠ 0)] [IsField γ]

private
def half_pos {ε: γ} (h: 0 < ε) : 0 < ε /? 2 ~((ne_of_lt two_pos).symm) := by
  sorry

local instance : AbsoluteValue α γ where
  abs := dist 0

def Eventually (P: Nat -> Prop) : Prop := ∃k, ∀n, k ≤ n -> P n
def Eventually₂ (P: Nat -> Nat -> Prop) : Prop := ∃k, ∀n m, k ≤ n -> k ≤ m -> P n m

def Eventually.to₂_left : Eventually a -> Eventually₂ fun i _ => a i := by
  intro ⟨i,hi⟩
  exists i
  intro n _ hn _
  apply hi; assumption

def Eventually.to₂_right : Eventually a -> Eventually₂ fun _ i => a i := by
  intro ⟨i,hi⟩
  exists i
  intro n _ hn _
  apply hi; assumption

def Eventually.merge : Eventually a -> Eventually b -> Eventually fun i => a i ∧ b i := by
  intro ⟨i,hi⟩ ⟨j,hj⟩
  exists max i j
  intro n hn
  apply And.intro
  apply hi
  apply le_trans _ hn
  apply le_max_left
  apply hj
  apply le_trans _ hn
  apply le_max_right

def Eventually₂.merge : Eventually₂ a -> Eventually₂ b -> Eventually₂ fun i j => a i j ∧ b i j := by
  intro ⟨i,hi⟩ ⟨j,hj⟩
  exists max i j
  intro m n hm hn
  apply And.intro
  apply hi
  apply le_trans _ hm
  apply le_max_left
  apply le_trans _ hn
  apply le_max_left
  apply hj
  apply le_trans _ hm
  apply le_max_right
  apply le_trans _ hn
  apply le_max_right

def is_cauchy_equiv (a b: Nat -> α) : Prop :=
  ∀ε: γ, 0 < ε -> Eventually₂ fun n m => dist (a n) (b m) < ε

structure CauchySeq (α: Type*) {γ: Type*} [Dist α γ] [Sub α] [LT γ] [Zero γ] where
  seq: Nat -> α
  is_cacuhy: is_cauchy_equiv seq seq

instance : FunLike (CauchySeq α) Nat α where
  coe := CauchySeq.seq
  coe_inj := by
    intro ⟨_, _⟩ ⟨_, _⟩ _; congr

attribute [coe] CauchySeq.seq

-- noncomputable so lean doesn't waste time compiling this
private noncomputable def findBoundFrom (f: Nat -> α) (src: α) : Nat -> γ
| 0 => 0
| n + 1 => max (dist src (f n)) (findBoundFrom f src n)

-- noncomputable so lean doesn't waste time compiling this
private noncomputable def findBound (f: Nat -> α) (k: Nat) : Nat -> γ
| 0 => 0
| n + 1 => max (findBoundFrom f (f n) k) (findBound f k n)

@[simp]
private def findBoundFrom.nonneg {f: Nat -> α} : 0 ≤ findBoundFrom f src n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [findBoundFrom, le_max_iff, ih]

@[simp]
private def findBound.nonneg {f: Nat -> α} : 0 ≤ findBound f k n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [findBound, le_max_iff, ih]

@[simp]
private def findBoundFrom.spec {f: Nat -> α} {k: Nat} : ∀n, n ≤ k -> dist src (f n) ≤ findBoundFrom f src k.succ := by
  induction k with
  | zero => intros n h; simp [findBoundFrom, le_max_iff]; left; rw [Nat.le_zero.mp h]
  | succ k ih =>
    intro n n_le
    rw [findBoundFrom]
    rcases Nat.lt_or_eq_of_le n_le with h | h
    replace n_le := Nat.le_of_lt_succ h
    apply le_trans (ih n n_le)
    simp [le_max_iff]
    subst n
    simp [le_max_iff]

@[simp]
private def findBound.spec {f: Nat -> α} {k₀ k₁: Nat} : ∀n m, n ≤ k₁ -> m ≤ k₀ -> dist (f n) (f m) ≤ findBound f k₀.succ k₁.succ := by
  intro n m nk mk
  induction k₁ with
  | zero =>
    cases Nat.le_zero.mp nk
    simp [findBound, le_max_iff]
    left
    apply findBoundFrom.spec
    assumption
  | succ k₁ ih =>
    rw [findBound, le_max_iff]
    have := findBoundFrom.spec (f := f) (k := k₀) (src := f (k₁+1)) m mk
    rcases lt_or_eq_of_le nk with nk | nk
    replace nk := Nat.le_of_lt_succ nk
    exact .inr (ih nk)
    left
    subst n
    apply this

def boundedDist (c: CauchySeq α) : ∃B: γ, ∀n m, dist (c n) (c m) < B := by
  have ⟨k, kspec⟩ := c.is_cacuhy 1 zero_lt_one
  dsimp at kspec
  have spec := findBound.spec (f := c) (k₀ := k) (k₁ := k)
  exists findBound c k.succ k.succ + 1
  intro n m
  rcases lt_or_le n k with n_lt_k | k_le_n
  <;> rcases lt_or_le m k with m_lt_k | k_le_m
  · have := spec n m (le_of_lt n_lt_k) (le_of_lt m_lt_k)
    apply lt_of_le_of_lt this
    conv => { lhs; rw [←add_zero (CauchySeq.findBound _ _ _)] }
    apply add_lt_add_of_le_of_lt
    rfl
    apply zero_lt_one
  · apply lt_of_le_of_lt
    apply dist_triangle (k := c k)
    apply add_lt_add_of_le_of_lt
    apply findBound.spec
    apply le_of_lt
    assumption
    rfl
    apply kspec
    rfl
    assumption
  · rw [dist_comm]
    apply lt_of_le_of_lt
    apply dist_triangle (k := c k)
    apply add_lt_add_of_le_of_lt
    apply findBound.spec
    apply le_of_lt
    assumption
    rfl
    apply kspec
    rfl
    assumption
  · apply lt_of_lt_of_le
    apply kspec
    assumption
    assumption
    conv => { lhs; rw [←zero_add 1] }
    apply add_le_add
    apply findBound.nonneg
    rfl

instance : Setoid (CauchySeq α) where
  r a b := is_cauchy_equiv a b
  iseqv := {
    refl x := x.is_cacuhy
    symm := by
      intro a b eqv ε ε_pos
      replace ⟨k, eqv⟩ := eqv ε ε_pos
      exists k
      intro n m kn km
      rw [dist_comm]
      apply eqv
      assumption
      assumption
    trans := by
      intro a b c ab bc ε ε_pos
      have := ab
      sorry
  }

def const (x: α) : CauchySeq α where
  seq _ := x
  is_cacuhy := by
    intro ε ε_pos
    exists 0
    intros
    dsimp
    rw [dist_self]
    assumption

instance : Zero (CauchySeq α) := ⟨const 0⟩

-- if a cauchy sequence converges to zero
def limZero (c: CauchySeq α) : Prop :=
  ∀ ε > 0, ∃ i, ∀ j ≥ i, ‖c j‖ < ε

-- def limZero_iff_eqv_zero

end CauchySeq
