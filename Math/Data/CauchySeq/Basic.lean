import Math.Algebra.Field.Order.Basic
import Math.Function.Basic
import Math.Ops.Abs
import Math.Topology.MetricSpace.Abs
import Math.Relation.Basic

namespace CauchySeq

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

def Eventually₂.wlog₀ (P: Nat -> Nat -> Prop) [Relation.IsSymmetric P] :
  (∃k, ∀n m, k ≤ n -> k ≤ m -> n ≤ m -> P n m) -> Eventually₂ P := by
  intro ⟨k, h⟩
  exists k
  intro n m hk hm
  rcases Nat.le_total n m with g | g
  apply h
  assumption
  assumption
  assumption
  apply Relation.symm
  apply h
  assumption
  assumption
  assumption

end CauchySeq

section

variable {α: Type*} [Norm α γ] [LT γ] [LE γ] [Zero γ] [Sub α]

def CauchySeq.is_cauchy_equiv (a b: Nat -> α) : Prop :=
  ∀ε: γ, 0 < ε -> Eventually₂ fun n m => ‖a n - b m‖ < ε

structure CauchySeq (α: Type*) {γ: Type*} [Norm α γ] [LT γ] [LE γ] [Zero γ] [Sub α] where
  seq: Nat -> α
  is_cacuhy: CauchySeq.is_cauchy_equiv seq seq

end

namespace CauchySeq

variable {α: Type*}
  [Norm α γ] [LatticeOps γ]
  [FieldOps γ] [IsField γ] [FieldOps α] [IsField α]
  [IsOrderedSemiring γ] [IsLinearLattice γ] [IsNontrivial γ]
  [IsLawfulNorm α]

open Norm.ofAbs

local instance : Dist α γ := Norm.instDist α
local instance : IsMetric α := Norm.instIsMetric α

section Helpers

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

def upper_bound (c: CauchySeq γ) : ∃B: γ, ∀n, c n < B := by
  have ⟨B, h⟩ := c.boundedDist
  exists B + |c 0|
  intro n
  apply lt_of_add_lt_add_right
  show c n + -c 0 < _
  rw [←sub_eq_add_neg, ←sub_eq_add_neg, add_sub_assoc]
  apply flip lt_of_le_of_lt
  apply lt_of_lt_of_le
  apply h n 0
  apply le_add_right
  apply le_of_add_le_add_right
  rw [sub_add_cancel, zero_add]
  apply le_abs_self
  apply le_abs_self

def upper_bound_with (c: CauchySeq γ) (u: γ) : ∃B: γ, u < B ∧ ∀n, c n < B := by
  have ⟨B, h⟩ := c.upper_bound
  exists B ⊔ (u + 1)
  apply And.intro
  apply flip lt_of_lt_of_le
  apply le_max_right
  rw (occs := [1]) [←add_zero u]
  apply add_lt_add_left
  apply zero_lt_one
  intro n
  apply lt_of_lt_of_le
  apply h
  apply le_max_left

instance setoid : Setoid (CauchySeq α) where
  r a b := is_cauchy_equiv a b
  iseqv := {
    refl x := x.is_cacuhy
    symm := by
      intro a b eqv ε ε_pos
      replace ⟨k, eqv⟩ := eqv ε ε_pos
      exists k
      intro n m kn km
      rw [norm_sub_comm]
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
      apply norm_add_le_add_norm
      rw [←add_half ε]
      apply add_lt_add
      apply lt_of_le_of_lt
      apply norm_add_le_add_norm
      rw [←add_half (ε /? 2)]
      apply add_lt_add
      assumption
      assumption
      rw [norm_sub_comm]
      assumption
  }

def eventually_pointwise (a b: CauchySeq α) :
  Eventually (fun i => a i = b i) -> a ≈ b := by
  intro h
  intro ε εpos
  have ⟨i, h⟩ := (b.is_cacuhy ε εpos).merge h.to₂_left
  exists i
  intro n m hn hm
  obtain ⟨h, hi⟩ := h n m hn hm
  rw [hi]
  apply h

def pointwise (a b: CauchySeq α) :
  (∀i, a i = b i) -> a ≈ b := by
  intro h
  apply eventually_pointwise
  exists 0
  intros; apply h

end  Helpers

def const.spec (x: α) : is_cauchy_equiv (fun _ => x) (fun _ => x) := by
  intro ε ε_pos
  exists 0
  intros
  dsimp
  rw [sub_self, norm_zero]
  assumption

def const (x: α) : CauchySeq α where
  seq _ := x
  is_cacuhy := by apply const.spec

section AddOps

instance : Zero (CauchySeq α) := ⟨const 0⟩

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
  apply norm_add_le_add_norm
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
  rw [neg_sub_neg, norm_sub_comm]
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

def norm.spec (a b: CauchySeq α) : a ≈ b ->
  is_cauchy_equiv (fun n => ‖a n‖) (fun n => ‖b n‖) := by
  intro ab ε ε_pos
  dsimp
  replace ⟨δ, ab⟩ := ab _ ε_pos
  refine ⟨δ, ?_⟩
  intro n m δ_le_n δ_le_m
  show |_| < _
  apply lt_of_le_of_lt
  apply abs_norm_sub_norm_le_norm_sub
  apply ab
  assumption
  assumption

def norm (a: CauchySeq α) : CauchySeq γ where
  seq n := ‖a n‖
  is_cacuhy := by
    apply CauchySeq.norm.spec
    rfl

instance : Norm (CauchySeq α) (CauchySeq γ) where
  norm := .norm

def nsmul.spec (a b: CauchySeq α) (n: ℕ) : a ≈ b ->
  is_cauchy_equiv (fun i => n • a i) (fun i => n • b i) := by
  intro eq
  induction n generalizing a b with
  | zero =>
    simp
    apply const.spec
  | succ n ih =>
    simp [succ_nsmul]
    let a' : CauchySeq α := ⟨_, ih a a (by rfl)⟩
    let b' : CauchySeq α := ⟨_, ih b b (by rfl)⟩
    apply add.spec a' a b' b
    apply ih
    assumption
    assumption

def nsmul (n: ℕ) (a: CauchySeq α) : CauchySeq α where
  seq i := n • a i
  is_cacuhy := by
    apply nsmul.spec
    rfl

instance : SMul ℕ (CauchySeq α) where
  smul := nsmul

def zsmul.spec (a b: CauchySeq α) (n: ℤ) : a ≈ b ->
  is_cauchy_equiv (fun i => n • a i) (fun i => n • b i) := by
  intro eq
  cases n with
  | ofNat n =>
    simp [zsmul_ofNat]
    apply nsmul.spec
    assumption
  | negSucc n =>
    simp [zsmul_negSucc]
    apply neg.spec ((n + 1) • a) ((n + 1) • b)
    apply nsmul.spec
    assumption

def zsmul (n: ℤ) (a: CauchySeq α) : CauchySeq α where
  seq i := n • a i
  is_cacuhy := by
    apply zsmul.spec
    rfl

instance : SMul ℤ (CauchySeq α) where
  smul := zsmul

end AddOps

-- if a cauchy sequence converges to zero
def IsLimZero (c: CauchySeq α) : Prop :=
  ∀ ε > 0, ∃ i, ∀ j ≥ i, ‖c j‖ < ε

def limZero_iff_eqv_zero (c: CauchySeq α) : c.IsLimZero ↔ c ≈ 0 := by
  apply Iff.intro
  intro h ε εpos
  have ⟨i, h⟩ := h ε εpos
  exists i
  intro n m hn hm
  show ‖c n - 0‖ < ε
  rw [sub_zero]; apply h
  assumption
  intro h ε εpos
  have ⟨i, h⟩ := h ε εpos
  exists i
  intro j hj
  rw [←sub_zero (c j)]
  apply h
  assumption
  assumption

def not_limZero_iff_not_eqv_zero (c: CauchySeq α) : ¬c.IsLimZero ↔ ¬c ≈ 0 := by
  apply Iff.not_iff_not
  apply limZero_iff_eqv_zero

def not_limZero_of_eqv (a b: CauchySeq α) (h: a ≈ b) (g: ¬a.IsLimZero) : ¬b.IsLimZero := by
  intro g₀; apply g
  rw [limZero_iff_eqv_zero] at *
  exact trans h g₀

instance : NatCast (CauchySeq α) := ⟨fun n => .const n⟩
instance : IntCast (CauchySeq α) := ⟨fun n => .const n⟩

-- instance : Zero (CauchySeq α) := ⟨.const 0⟩
instance : One (CauchySeq α) := ⟨.const 1⟩

instance : AddMonoidWithOneOps (CauchySeq α) := _root_.instAddMonoidOpsWithOne
instance : AddGroupWithOneOps (CauchySeq α) := instAddGroupWithOneOpsOfAddMonoidWithOneOpsOfNegOfSubOfIntCastOfSMulInt

@[ext]
def ext (a b: CauchySeq α) : (∀i, a i = b i) -> a = b := DFunLike.ext _ _

instance : IsAddCommMagma (CauchySeq α) where
  add_comm a b := by ext; apply add_comm

instance : IsAddGroup (CauchySeq α) where
  add_assoc _ _ _ := by ext; apply add_assoc
  zero_add _ := by ext; apply zero_add
  add_zero _ := by ext; apply add_zero
  sub_eq_add_neg _ _ := by ext; apply sub_eq_add_neg
  zero_nsmul _ := by ext; apply zero_nsmul
  succ_nsmul _ _ := by ext; apply succ_nsmul
  zsmul_ofNat _ _ := by ext; apply zsmul_ofNat
  zsmul_negSucc _ _ := by ext; apply zsmul_negSucc
  neg_add_cancel _ := by ext; apply neg_add_cancel

section Order

def Pos (a: CauchySeq γ) : Prop := ∃B, 0 < B ∧ Eventually fun i => B ≤ a i

def Pos.spec (a b: CauchySeq γ) (ab: a ≈ b) (pos: a.Pos) : b.Pos := by
  replace ⟨B, B_pos, pos⟩ := pos
  refine ⟨_, half_pos B_pos, ?_⟩
  obtain ⟨K, prf⟩ := pos
  replace ⟨δ, ab⟩ := ab _ (half_pos B_pos)
  simp at ab prf
  refine ⟨max K δ, ?_⟩
  intro n Kδ_le_n
  apply le_trans _ (sub_abs_self_sub (a n) (b n))
  apply flip le_trans
  apply sub_le_sub
  apply prf
  apply (max_le_iff.mp Kδ_le_n).left
  apply le_of_lt;
  apply ab
  iterate 2 apply (max_le_iff.mp Kδ_le_n).right
  conv => {
    rhs; lhs; rw [←mul_div?_cancel B 2 (NeZero.ne 2)]
  }
  rw [two_mul, add_sub_assoc, add_sub_cancel]

instance : LT (CauchySeq γ) where
  lt a b := (b - a).Pos

instance : LE (CauchySeq γ) where
  le a b := a < b ∨ a ≈ b

end Order

def non_zero_of_Pos (a: CauchySeq γ) : a.Pos -> ¬a ≈ 0 := by
  classical
  intro pos eq_zero
  obtain ⟨B, B_pos, pos⟩ := pos
  replace ⟨δ, prf⟩  := pos.to₂_right.merge (eq_zero _ B_pos)
  replace ⟨pos, eq_zero⟩ := prf δ δ (le_refl _) (le_refl _)
  clear prf
  replace eq_zero : |_ - 0| < B := eq_zero
  erw [sub_zero, abs_def] at eq_zero
  split at eq_zero <;> rename_i h
  exact lt_irrefl <| lt_of_lt_of_le eq_zero pos
  rw [not_le] at h
  exact lt_asymm B_pos (lt_of_le_of_lt pos h)

def norm_pos_of_not_zero (f: CauchySeq α) (hf: ¬f ≈ 0) : 0 < ‖f‖ := by
  false_or_by_contra
  rename_i nk

  refine hf fun ε ε_pos => ?_
  replace nk : ∀ (x : γ), 0 < x → ∀ (y : Nat), ∃ z, ∃ (_ : y ≤ z), ‖f z‖ < x := by
    intro x hx n
    have nk := not_exists.mp (not_and.mp (not_exists.mp nk x) hx) n
    have ⟨m,prf⟩ := Classical.not_forall.mp nk
    have ⟨hm,prf⟩ := Classical.not_imp.mp prf
    exists m
    exists hm
    apply lt_of_not_le
    replace prf : ¬ (x ≤ ‖f m‖ - 0) := prf
    simpa using prf

  have ⟨i,hi⟩ := f.is_cacuhy _ (half_pos ε_pos)
  rcases nk _ (half_pos ε_pos) i with ⟨j, ij, hj⟩
  refine ⟨j, fun k _ jk _ => ?_⟩
  simp
  erw [sub_zero]
  have := lt_of_le_of_lt (norm_add_le_add_norm _ _) (add_lt_add _ _ _ _ (hi k j (le_trans ij jk) ij) hj)
  erw [sub_eq_add_neg, add_assoc, neg_add_cancel] at this
  rwa [add_zero, ←mul_two, div?_mul_cancel] at this

end CauchySeq

namespace CauchySeq

variable {α: Type*}
  [Norm α γ] [LatticeOps γ]
  [FieldOps γ] [IsField γ] [FieldOps α] [IsField α]
  [IsOrderedSemiring γ] [IsLinearLattice γ]
  [IsAlgebraNorm α]

open Norm.ofAbs

local instance : IsLinearOrder γ := (inferInstanceAs (IsLinearLattice γ)).toIsLinearOrder
local instance : Dist α γ := Norm.instDist α
local instance : IsMetric α := Norm.instIsMetric α

def mul.spec (a b c d: CauchySeq α) : a ≈ c -> b ≈ d ->
  is_cauchy_equiv (fun n => a n * b n) (fun n => c n * d n) := by
  intro ac bd ε ε_pos
  simp
  have ⟨amax, one_lt_amax, amax_spec⟩ := ‖a‖.upper_bound_with 1
  have ⟨dmax, one_lt_dmax, dmax_spec⟩ := ‖d‖.upper_bound_with 1

  have amax_pos : 0 < amax := lt_trans zero_lt_one one_lt_amax
  have dmax_pos : 0 < dmax := lt_trans zero_lt_one one_lt_dmax

  have amax_nonzero := (ne_of_lt amax_pos).symm
  have dmax_nonzero := (ne_of_lt dmax_pos).symm

  let ε₀ := (ε /? 2) /? dmax
  let ε₁ := (ε /? 2) /? amax

  have ε₀_pos : 0 < ε₀ := by
    apply div?_pos
    apply div?_pos
    assumption
    apply two_pos
    assumption
  have ε₁_pos : 0 < ε₁ := by
    apply div?_pos
    apply div?_pos
    assumption
    apply two_pos
    assumption

  -- = |a b - c d + a d - a d|
  -- = |a b - a d - c d + a d|
  -- = |a b - a d + a d - c d|
  -- = |a (b - d) + (a - c) d|
  -- ≤ |a (b - d)| + |(a - c) d|
  -- = |a| |(b - d)| + |(a - c)| |d|
  -- < amax ε/(2 amax) + (ε/(2 dmax)) dmax
  -- = ε/2 + ε/2
  -- = ε

  have ⟨δ, prf⟩ := (ac _ ε₀_pos).merge (bd _ ε₁_pos)
  refine ⟨δ, ?_⟩
  intro n m δ_le_n δ_le_m
  replace ⟨ab, bd⟩ := prf _ _ δ_le_n δ_le_m
  rw [←add_zero (_ - _), ←add_neg_cancel (a n * d m),
    sub_eq_add_neg]
  have :
    a n * b n + -(c m * d m) + (a n * d m + -(a n * d m)) =
    a n * b n + -(a n * d m) + (a n * d m + -(c m * d m)) := by ac_rfl
  rw [this]; clear this
  iterate 2 rw [←sub_eq_add_neg]
  rw [←mul_sub, ←sub_mul]
  apply lt_of_le_of_lt
  apply norm_add_le_add_norm
  rw [norm_mul, norm_mul]
  apply lt_of_le_of_lt (b := amax * _ + _ * dmax)
  apply add_le_add
  apply mul_le_mul_of_nonneg_right
  apply le_of_lt
  apply amax_spec
  apply norm_nonneg
  apply mul_le_mul_of_nonneg_left
  apply le_of_lt
  apply dmax_spec
  apply norm_nonneg
  apply lt_of_lt_of_le
  apply add_lt_add_of_lt_of_le
  apply (lt_iff_mul_lt_mul_of_pos_left _ _ _ _).mp
  assumption
  assumption
  apply (le_iff_mul_le_mul_of_pos_right _ _ _ _).mp
  apply le_of_lt
  assumption
  assumption
  rw [div?_mul_cancel, mul_div?_cancel, add_half]

def mul (a b: CauchySeq α) : CauchySeq α where
  seq n := a n * b n
  is_cacuhy := by apply CauchySeq.mul.spec <;> rfl

instance : Mul (CauchySeq α) := ⟨.mul⟩

def npow.spec (a b: CauchySeq α) (n: ℕ) : a ≈ b ->
  is_cauchy_equiv (fun i => a i ^ n) (fun i => b i ^ n) := by
  intro eq
  induction n generalizing a b with
  | zero =>
    simp
    apply const.spec
  | succ n ih =>
    simp [npow_succ]
    let a' : CauchySeq α := ⟨_, ih a a (by rfl)⟩
    let b' : CauchySeq α := ⟨_, ih b b (by rfl)⟩
    apply mul.spec a' a b' b
    apply ih
    assumption
    assumption

def npow (a: CauchySeq α) (n: ℕ) : CauchySeq α where
  seq i := a i ^ n
  is_cacuhy := by
    apply npow.spec
    rfl

instance : Pow (CauchySeq α) ℕ where
  pow := npow

variable [DecidableEq α]

def safe_inv (a: CauchySeq α) (i: ℕ): α :=
  if hb:a i = 0 then 0 else (a i)⁻¹?

def inv.spec (a b: CauchySeq α) : a ≈ b -> ¬a ≈ 0 -> is_cauchy_equiv (safe_inv a) (safe_inv b) := by
  intro ab ha
  have hb := not_limZero_of_eqv _ _ ab ((not_limZero_iff_not_eqv_zero _).mpr ha)
  rw [not_limZero_iff_not_eqv_zero] at hb
  intro ε εpos
  have ⟨A, Apos, hA⟩ := norm_pos_of_not_zero a ha
  have ⟨B, Bpos, hB⟩ := norm_pos_of_not_zero b hb
  simp at hA hB
  have : 0 < A * B := by
    apply mul_pos
    assumption
    assumption

  have ⟨δ, h⟩ := (ab (ε * (A * B)) (by
    apply mul_pos
    exact εpos
    assumption)).merge (hA.to₂_left.merge hB.to₂_right)
  exists δ
  intro n m hn hm
  have ⟨h, hA, hB⟩ := h _ _ hn hm
  replace hA : A ≤ ‖a n‖ := hA; replace hB : B ≤ ‖b m‖ := hB
  have anez : a n ≠ 0 := by
    intro h; rw [h, norm_zero] at hA
    have := not_lt_of_le hA; contradiction
  have bnez : b m ≠ 0 := by
    intro h; rw [h, norm_zero] at hB
    have := not_lt_of_le hB; contradiction
  unfold safe_inv; rw [dif_neg anez, dif_neg bnez]
  rw [inv_sub_inv, norm_div?, norm_sub_comm]
  conv => { lhs; arg 2; rw [norm_mul] }
  rw [div?_eq_mul_inv?]
  apply lt_of_lt_of_le
  · show _ < (ε * (A * B)) * (A * B)⁻¹?
    apply lt_of_lt_of_le
    apply mul_lt_mul_of_pos_right
    apply h
    apply inv?_pos
    apply mul_pos
    apply lt_of_lt_of_le _ hA
    assumption
    apply lt_of_lt_of_le _ hB
    assumption
    apply mul_le_mul_of_nonneg_left
    apply (inv?_le_inv? _ _ _ _).mpr
    apply le_trans
    apply mul_le_mul_of_nonneg_left
    apply hB
    apply le_of_lt; assumption
    apply mul_le_mul_of_nonneg_right
    apply hA
    apply norm_nonneg
    apply mul_pos
    apply lt_of_lt_of_le _ hA
    assumption
    apply lt_of_lt_of_le _ hB
    assumption
    apply mul_pos
    assumption
    assumption
    apply le_of_lt
    apply mul_pos
    assumption
    apply mul_pos
    assumption
    assumption
  · rw [mul_assoc, mul_inv?_cancel, mul_one]

def inv (a: CauchySeq α) (h: ¬a ≈ 0) : CauchySeq α where
  seq := a.safe_inv
  is_cacuhy := by
    apply inv.spec
    rfl
    assumption

end CauchySeq
