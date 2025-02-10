import Math.Order.Linear
import Math.Function.Basic
import Math.Ops.Abs
import Math.Topology.MetricSpace.Abs
import Math.Relation.Basic

namespace CauchySeq

open Abs

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

end CauchySeq

section

variable {α: Type*} [AbsoluteValue α γ] [LT γ] [LE γ] [Zero γ] [Sub α]


def CauchySeq.is_cauchy_equiv (a b: Nat -> α) : Prop :=
  ∀ε: γ, 0 < ε -> Eventually₂ fun n m => ‖a n - b m‖ < ε

structure CauchySeq (α: Type*) {γ: Type*} [AbsoluteValue α γ] [LT γ] [LE γ] [Zero γ] [Sub α] where
  seq: Nat -> α
  is_cacuhy: CauchySeq.is_cauchy_equiv seq seq

end
namespace CauchySeq

variable {α: Type*} [AbsoluteValue α γ]
  [FieldOps γ] [LT γ] [LE γ] [Min γ] [Max γ]
  [IsField γ] [IsLinearMinMaxOrder γ] [IsOrderedRing γ]
  [FieldOps α] [IsField α] [IsOrderedAbsRing α]

local instance : IsLinearOrder γ := (inferInstanceAs (IsLinearMinMaxOrder γ)).toIsLinearOrder
local instance : Dist α γ := Abs.instDist α
local instance : IsMetricSpace α := Abs.instIsMetricSpace α
local instance : @Std.Commutative α (· + ·) := ⟨add_comm⟩
local instance :  @Std.Associative α (· + ·) := ⟨add_assoc⟩

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
private noncomputable def findBound (f g: Nat -> α) (k: Nat) : Nat -> γ
| 0 => 0
| n + 1 => max (findBoundFrom f (g n) k) (findBound f g k n)

@[simp]
private def findBoundFrom.nonneg {f: Nat -> α} : 0 ≤ findBoundFrom f src n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [findBoundFrom, le_max_iff, ih]

@[simp]
private def findBound.nonneg {f g: Nat -> α} : 0 ≤ findBound f g k n := by
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
private def findBound.spec {f g: Nat -> α} {k₀ k₁: Nat} : ∀n m, n ≤ k₁ -> m ≤ k₀ -> dist (g n) (f m) ≤ findBound f g k₀.succ k₁.succ := by
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
    have := findBoundFrom.spec (f := f) (k := k₀) (src := g (k₁+1)) m mk
    rcases lt_or_eq_of_le nk with nk | nk
    replace nk := Nat.le_of_lt_succ nk
    exact .inr (ih nk)
    left
    subst n
    apply this

def boundedDistBetween {f g: Nat -> α} (c: is_cauchy_equiv f g) : ∃B: γ, ∀n m, dist (g n) (f m) < B := by
  have ⟨k, kspec⟩ := c 1 zero_lt_one
  dsimp at kspec
  have spec := findBound.spec (f := f) (g := g) (k₀ := k) (k₁ := k)
  exists findBound f g k.succ k.succ + 1
  intro n m
  rcases lt_or_le n k with n_lt_k | k_le_n
  <;> rcases lt_or_le m k with m_lt_k | k_le_m
  · have := spec n m (le_of_lt n_lt_k) (le_of_lt m_lt_k)
    apply lt_of_le_of_lt this
    conv => { lhs; rw [←add_zero (CauchySeq.findBound _ _ _ _)] }
    apply add_lt_add_of_le_of_lt
    rfl
    apply zero_lt_one
  · show ‖g n - f m‖ < _
    apply lt_of_le_of_lt

    -- apply lt_of_le_of_lt
    -- apply dist_triangle (k := f k)
    -- apply add_lt_add_of_le_of_lt
    -- apply findBound.spec
    -- apply le_of_lt
    -- assumption
    -- rfl
    -- apply kspec
    -- rfl
    assumption
  · rw [dist_comm]
    apply lt_of_le_of_lt
    apply dist_triangle (k := f k)
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

def boundedDist (c: CauchySeq α) : ∃B: γ, ∀n m, dist (c n) (c m) < B := by
  have ⟨k, kspec⟩ := c.is_cacuhy 1 zero_lt_one
  dsimp at kspec
  have spec := findBound.spec (f := c) (g := c) (k₀ := k) (k₁ := k)
  exists findBound c c k.succ k.succ + 1
  intro n m
  rcases lt_or_le n k with n_lt_k | k_le_n
  <;> rcases lt_or_le m k with m_lt_k | k_le_m
  · have := spec n m (le_of_lt n_lt_k) (le_of_lt m_lt_k)
    apply lt_of_le_of_lt this
    conv => { lhs; rw [←add_zero (CauchySeq.findBound _ _ _ _)] }
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

instance setoid : Setoid (CauchySeq α) where
  r a b := is_cauchy_equiv a b
  iseqv := {
    refl x := x.is_cacuhy
    symm := by
      intro a b eqv ε ε_pos
      replace ⟨k, eqv⟩ := eqv ε ε_pos
      exists k
      intro n m kn km
      rw [abs_sub_comm]
      apply eqv
      assumption
      assumption
    trans := by
      intro a b c ab bc ε ε_pos
      have ⟨k, spec⟩ := (ab _ (half_pos (half_pos ε_pos))).merge (bc _ (half_pos (half_pos ε_pos)))
        |>.merge (b.is_cacuhy _ (half_pos ε_pos))
      exists k
      intro n m kn km
      replace ⟨⟨ab, bc⟩, bspec⟩ := spec n m kn km
      rw [←add_zero (_ - _), ←add_neg_cancel (b m), ←add_zero (_ - _), ←add_neg_cancel (b n),
        sub_eq_add_neg]
      rw [show a n + -c m + (b n + -b n) + (b m + -b m) =
               (a n + -b m) + (b n + -c m) + (b m + -b n) by ac_rfl]
      rw [←sub_eq_add_neg, ←sub_eq_add_neg, ←sub_eq_add_neg]
      have : (2: γ) ≠ 0 := by symm; apply ne_of_lt; exact two_pos
      apply lt_of_le_of_lt
      apply abs_add_le_add_abs
      rw [←add_half ε]
      apply add_lt_add
      apply lt_of_le_of_lt
      apply abs_add_le_add_abs
      rw [←add_half (ε /? 2)]
      apply add_lt_add
      assumption
      assumption
      rw [abs_sub_comm]
      assumption
  }

def const (x: α) : CauchySeq α where
  seq _ := x
  is_cacuhy := by
    intro ε ε_pos
    exists 0
    intros
    dsimp
    rw [sub_self, abs_zero.mpr]
    assumption
    rfl

instance : Zero (CauchySeq α) := ⟨const 0⟩

-- if a cauchy sequence converges to zero
def IsLimZero (c: CauchySeq α) : Prop :=
  ∀ ε > 0, ∃ i, ∀ j ≥ i, ‖c j‖ < ε

def add.spec (a b c d: CauchySeq α) : a ≈ c -> b ≈ d -> is_cauchy_equiv (fun n => a n + b n) (fun n => c n + d n) := by
  intro ac bd ε ε_pos
  have ⟨k, spec⟩ := (ac _ (half_pos ε_pos)).merge (bd _ (half_pos ε_pos))
  exists k
  intro n m kn km
  replace spec := spec n m kn km
  obtain ⟨ac, bd⟩ := spec
  dsimp
  rw [sub_eq_add_neg, neg_add_rev, show a n + b n + (-d m + -c m) = (a n + -c m) + (b n + -d m) by ac_rfl]
  rw [←sub_eq_add_neg, ←sub_eq_add_neg, ←add_half ε]
  apply lt_of_le_of_lt
  apply abs_add_le_add_abs
  apply add_lt_add
  assumption
  assumption

def add (a b: CauchySeq α) : CauchySeq α where
  seq n := a n + b n
  is_cacuhy := by
    apply add.spec
    apply a.is_cacuhy
    apply b.is_cacuhy

instance : Add (CauchySeq α) := ⟨.add⟩

def neg.spec (a b: CauchySeq α) : a ≈ b -> is_cauchy_equiv (fun n => -a n) (fun n => -b n) := by
  intro ab ε ε_pos
  replace ⟨k, ab⟩ := ab _ ε_pos
  exists k
  intro n m kn km
  replace ab := ab n m kn km
  dsimp
  dsimp at ab
  rw [neg_sub_neg, abs_sub_comm]
  assumption

def neg (a: CauchySeq α) : CauchySeq α where
  seq n := -a n
  is_cacuhy := by
    apply neg.spec
    apply a.is_cacuhy

instance : Neg (CauchySeq α) := ⟨.neg⟩

def sub.spec (a b c d: CauchySeq α) : a ≈ c -> b ≈ d -> is_cauchy_equiv (fun n => a n - b n) (fun n => c n - d n) := by
  intro ac bd
  conv => { arg 1; intro n; rw [sub_eq_add_neg] }
  conv => { arg 2; intro n; rw [sub_eq_add_neg] }
  apply add.spec (a := a) (b := -b) (c := c) (d := -d)
  assumption
  apply neg.spec
  assumption

def sub (a b: CauchySeq α) : CauchySeq α where
  seq n := a n - b n
  is_cacuhy := by
    apply sub.spec
    apply a.is_cacuhy
    apply b.is_cacuhy

instance : Sub (CauchySeq α) := ⟨.sub⟩

def mul.spec (a b c d: CauchySeq α): a ≈ c -> b ≈ d -> is_cauchy_equiv (fun n => a n * b n) (fun n => c n * d n) := by
  intro ac bd ε ε_pos
  have ⟨K₁, K₁spec⟩ := a.boundedDist
  have ⟨K₂, K₂spec⟩ := d.boundedDist
  let B := max 1 (max K₁ K₂)
  have bound_pos' : 0 < B := by
    apply lt_of_lt_of_le zero_lt_one
    apply le_max_left
  have bound_pos : 0 < 2 * B := by
    rw [←mul_zero 2]
    apply mul_lt_mul_of_pos_left
    assumption
    apply two_pos
  have : 2 * B ≠ 0 := by
    symm; apply ne_of_lt
    assumption

  obtain ⟨δ, spec⟩  := (ac _ (div?_pos _ _ ε_pos bound_pos)).merge (bd _ (div?_pos _ _ ε_pos bound_pos))
  exists δ
  intro n m δn δm
  obtain ⟨ac, bd⟩ := spec _ _ δn δm
  dsimp
  replace ac := mul_lt_mul_of_pos_right _ _ ac _ bound_pos'
  conv at ac => {
    rhs
    rw [div?_eq_mul_inv?, mul_assoc, inv?_mul_rev _ _ (by
      have := two_pos (α := γ)
      invert_tactic), mul_comm _ B, ←mul_assoc B, mul_inv?_cancel _ (by
      invert_tactic), one_mul, ←div?_eq_mul_inv?]
  }
  replace bd := mul_lt_mul_of_pos_right _ _ bd _ bound_pos'
  conv at bd => {
    rhs
    rw [div?_eq_mul_inv?, mul_assoc, inv?_mul_rev _ _ (by
      have := two_pos (α := γ)
      invert_tactic), mul_comm _ B, ←mul_assoc B, mul_inv?_cancel _ (by
      invert_tactic), one_mul, ←div?_eq_mul_inv?]
  }
  rw [←add_half ε]
  apply flip lt_of_le_of_lt
  apply add_lt_add
  exact ac
  exact bd
  rw [←add_mul]
  apply flip le_trans
  apply mul_le_mul_of_nonneg_right
  apply abs_add_le_add_abs
  apply le_of_lt; assumption
  clear ac bd



  sorry

end CauchySeq

section

variable (α: Type*) {γ: Type*} [AbsoluteValue α γ]
  [FieldOps γ] [LT γ] [LE γ] [Min γ] [Max γ]
  [IsField γ] [IsLinearMinMaxOrder γ] [IsOrderedRing γ]
  [FieldOps α] [IsField α] [IsOrderedAbsRing α]

def Cauchy := Quotient (CauchySeq.setoid (α := α))

end

namespace Cauchy

variable {α: Type*} {γ: Type*} [AbsoluteValue α γ]
  [FieldOps γ] [LT γ] [LE γ] [Min γ] [Max γ]
  [IsField γ] [IsLinearMinMaxOrder γ] [IsOrderedRing γ]
  [FieldOps α] [IsField α] [IsOrderedAbsRing α]

def mk : CauchySeq α -> Cauchy α := Quotient.mk _

scoped notation "⟦" x "⟧" => mk x

def add : Cauchy α -> Cauchy α -> Cauchy α := by
  apply Quotient.lift₂ (⟦· + ·⟧)
  intro a b c d ac bd
  apply Quotient.sound
  apply CauchySeq.add.spec
  assumption
  assumption

instance : Add (Cauchy α) := ⟨.add⟩

def neg : Cauchy α -> Cauchy α := by
  apply Quotient.lift (⟦-·⟧)
  intro a b ab
  apply Quotient.sound
  apply CauchySeq.neg.spec
  assumption

instance : Neg (Cauchy α) := ⟨.neg⟩

def sub : Cauchy α -> Cauchy α -> Cauchy α := by
  apply Quotient.lift₂ (⟦· - ·⟧)
  intro a b c d ac bd
  apply Quotient.sound
  apply CauchySeq.sub.spec
  assumption
  assumption

instance : Sub (CauchySeq α) := ⟨.sub⟩

end Cauchy
