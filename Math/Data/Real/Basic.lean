import Math.Data.Rat.OrderedAlgebra
import Math.Function.Basic

def CauchySeq.Eventually (P: Nat -> Prop) : Prop := ∃k, ∀n, k ≤ n -> P n
def CauchySeq.Eventually₂ (P: Nat -> Nat -> Prop) : Prop := ∃k, ∀n m, k ≤ n -> k ≤ m -> P n m

def CauchySeq.Eventually.to₂_left : Eventually a -> Eventually₂ fun i _ => a i := by
  intro ⟨i,hi⟩
  exists i
  intro n _ hn _
  apply hi; assumption

def CauchySeq.Eventually.to₂_right : Eventually a -> Eventually₂ fun _ i => a i := by
  intro ⟨i,hi⟩
  exists i
  intro n _ hn _
  apply hi; assumption

def CauchySeq.Eventually.merge : Eventually a -> Eventually b -> Eventually fun i => a i ∧ b i := by
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

def CauchySeq.Eventually₂.merge : Eventually₂ a -> Eventually₂ b -> Eventually₂ fun i j => a i j ∧ b i j := by
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

def CauchySeq.Eventually₂.lower_bound (n: Nat) : Eventually₂ fun i j => n ≤ i ∧ n ≤ j := by
  exists n
  intro i j ni nj
  trivial

def is_cauchy_equiv (a b: Nat -> ℚ) : Prop :=
  ∀ε: ℚ, 0 < ε -> CauchySeq.Eventually₂ fun n m => ‖a n - b m‖ < ε

structure CauchySeq where
  seq: Nat -> ℚ
  is_cacuhy: is_cauchy_equiv seq seq

instance : CoeFun CauchySeq (fun _ => Nat -> ℚ) := ⟨CauchySeq.seq⟩

-- noncomputable so lean doesn't waste time compiling this
noncomputable def CauchySeq.max_until (c: CauchySeq) (limit: Nat) : ℚ :=
  limit.succ.rec (motive := fun _ => ℚ) (c 0) (fun n acc => max acc (c n))

def CauchySeq.max_until.spec (c: CauchySeq) (limit: Nat) : ∀n ≤ limit, c n ≤ c.max_until limit := by
  intro n le
  induction limit generalizing n with
  | zero =>
    cases Nat.le_zero.mp le
    unfold max_until
    simp
    apply le_max_left
  | succ limit ih =>
    cases lt_or_eq_of_le le
    rename_i le
    replace le := Nat.le_of_lt_succ le
    apply le_trans
    apply ih
    assumption
    apply le_max_left
    subst n
    apply le_max_right

def CauchySeq.upper_bound (c: CauchySeq) : ∃bound: ℚ, ∀n, c n < bound := by
  have ⟨δ, h⟩  := c.is_cacuhy 1 (by decide)
  let max := c.max_until δ
  exists max + 1
  intro n
  simp at h
  if g:n ≤ δ then
    apply lt_of_le_of_lt
    apply max_until.spec c δ
    assumption
    rw [←add_zero (c.max_until δ)]
    apply Rat.add_lt_add_of_le_of_lt
    rfl
    decide
  else
    suffices c δ + ‖c n - c δ‖ < max + 1 by
      apply lt_of_le_of_lt _ this
      rw [Rat.abs_def]
      split <;> rename_i g
      rw [add_sub_cancel]
      apply le_trans
      show c n ≤ c δ
      rw [not_le, ←Rat.lt_add_iff_sub_lt, zero_add] at g
      apply le_of_lt; assumption
      apply Rat.le_add_right_nonneg
      rw [not_le] at g
      rw [Rat.neg_le_neg_iff, neg_neg]
      apply le_of_lt; assumption
    apply Rat.add_lt_add_of_le_of_lt
    apply max_until.spec c δ
    rfl
    exact h n δ (le_of_lt (lt_of_not_le g)) (le_refl _)

def CauchySeq.upper_bound_with (c: CauchySeq) (b: ℚ) : ∃bound: ℚ, b ≤ bound ∧ ∀n, c n < bound := by
  have ⟨bound, prf⟩  := c.upper_bound
  exists max bound b
  apply And.intro
  apply le_max_right
  intro n
  apply lt_of_lt_of_le
  apply prf
  apply le_max_left

def CauchySeq.Equiv (a b: CauchySeq) := is_cauchy_equiv a.seq b.seq

def Rat.half_pos {ε: ℚ} : 0 < ε -> 0 < ε /? 2 := (Rat.mul_pos · (by decide))

@[refl]
def CauchySeq.Equiv.refl (a: CauchySeq) : Equiv a a := a.is_cacuhy
@[symm]
def CauchySeq.Equiv.symm {a b: CauchySeq} : Equiv a b -> Equiv b a := by
  intro h ε ε_pos
  replace ⟨δ, h⟩ := h ε ε_pos
  exists δ
  intro n m _ _
  rw [abs_sub_comm]
  apply h <;> assumption
def CauchySeq.Equiv.trans {a b c: CauchySeq} : Equiv a b -> Equiv b c -> Equiv a c := by
  intro ab bc ε ε_pos
  replace ab := ab _ (Rat.half_pos ε_pos)
  replace bc := bc _ (Rat.half_pos (Rat.half_pos ε_pos))
  replace bspec := b.is_cacuhy _ (Rat.half_pos (Rat.half_pos ε_pos))
  have ⟨δ, h⟩ := ab.merge (bc.merge bspec)
  exists δ
  intro n m δ_le_n δ_le_m
  replace ⟨ab, bc, bspec⟩ := h n m δ_le_n δ_le_m
  have := Rat.add_lt_add ab (Rat.add_lt_add bc bspec)
  rw [←mul_two, div?_mul_cancel, ←mul_two, div?_mul_cancel,
    abs_sub_comm (b n) (b m)] at this
  apply lt_of_le_of_lt _ this
  apply flip le_trans
  apply Rat.add_le_add
  rfl
  apply Rat.abs_add_le_add_abs
  apply flip le_trans
  apply Rat.abs_add_le_add_abs
  iterate 4 rw [sub_eq_add_neg]
  have : a n + -b m + (b n + -c m + (b m + -b n)) =
    a n + -c m + (-b m + b m) + (b n + -b n) := by ac_rfl
  rw [this]; clear this
  rw [neg_add_cancel, add_neg_cancel, add_zero, add_zero]

instance CauchySeq.setoid : Setoid CauchySeq := ⟨Equiv, Equiv.refl, Equiv.symm, Equiv.trans⟩

def Real := Quotient CauchySeq.setoid
notation "ℝ" => Real
def Real.mk : CauchySeq -> ℝ := Quotient.mk _

local notation "⟦" v "⟧" => Real.mk v

@[cases_eliminator]
def Real.ind {motive: ℝ -> Prop} : (mk: ∀x, motive ⟦x⟧) -> ∀r, motive r := Quotient.ind
@[cases_eliminator]
def Real.ind₂ {motive: ℝ -> ℝ -> Prop} : (mk: ∀x y, motive ⟦x⟧ ⟦y⟧) -> ∀x y, motive x y := Quotient.ind₂
@[cases_eliminator]
def Real.ind₃ {motive: ℝ -> ℝ -> ℝ -> Prop} : (mk: ∀x y z, motive ⟦x⟧ ⟦y⟧ ⟦z⟧) -> ∀x y z, motive x y z := by
  intro h x y z
  induction x using ind with | mk x =>
  induction y using ind with | mk y =>
  induction z using ind with | mk z =>
  apply h

def CauchySeq.ofRat (q: ℚ) : CauchySeq where
  seq _ := q
  is_cacuhy ε ε_pos := by
    refine ⟨0, ?_⟩
    intro n m _ _
    simp
    assumption

def Real.ofRat (q: ℚ) : ℝ := ⟦.ofRat q⟧

@[refl]
def CauchySeq.refl (a: CauchySeq) : a ≈ a := CauchySeq.Equiv.refl a
@[symm]
def CauchySeq.symm {a b: CauchySeq} : a ≈ b -> b ≈ a := CauchySeq.Equiv.symm

def CauchySeq.pointwise (a b: CauchySeq) : (∀n, a n = b n) -> a ≈ b := by
  intro h
  suffices a = b by rw [this]
  cases a; cases b
  congr
  funext
  apply h

def CauchySeq.eventually_pointwise (a b: CauchySeq) : Eventually (fun n => a n = b n) -> a ≈ b := by
  intro eq
  intro ε ε_pos
  have ⟨δ, prf⟩ := eq.to₂_right.merge (a.is_cacuhy ε ε_pos)
  refine ⟨δ, ?_⟩
  intro n m δn δm
  replace ⟨eq, prf⟩ := prf _ _ δn δm
  rw [←eq]
  assumption

instance : Coe ℚ ℝ := ⟨.ofRat⟩
instance : Coe ℚ ℝ := ⟨.ofRat⟩
instance : NatCast ℝ where
  natCast n := (n: ℚ)
instance : IntCast ℝ where
  intCast n := (n: ℚ)
instance : OfNat CauchySeq n := ⟨.ofRat n⟩
instance : OfNat ℝ n := ⟨n⟩

instance : Nonempty ℝ := ⟨0⟩

def CauchySeq.add.spec (a b c d: CauchySeq) :
  a ≈ c -> b ≈ d ->
  is_cauchy_equiv (fun n => a n + b n) (fun n => c n + d n) := by
  intro ac bd ε ε_pos
  have ⟨δ, h⟩ := (ac _ (Rat.half_pos ε_pos)).merge (bd _ (Rat.half_pos ε_pos))
  refine ⟨δ, ?_⟩
  intro n m δ_le_n δ_le_m
  show ‖a n + b n - (c m + d m)‖ < ε
  rw [sub_eq_add_neg, neg_add_rev]
  have : ‖a n + b n + (-d m + -c m)‖ =
    ‖a n + -c m + (b n + -d m)‖ := by ac_rfl
  rw [this]; clear this
  replace ⟨ab, cd⟩  := h n m δ_le_n δ_le_m
  have := Rat.add_lt_add ab cd
  rw [←mul_two, div?_mul_cancel] at this
  apply lt_of_le_of_lt _ this
  rw [←sub_eq_add_neg, ←sub_eq_add_neg]
  apply Rat.abs_add_le_add_abs

def CauchySeq.add (a b: CauchySeq) : CauchySeq where
  seq n := a n + b n
  is_cacuhy := by apply CauchySeq.add.spec <;> rfl

instance : Add CauchySeq := ⟨.add⟩

def Real.add : ℝ -> ℝ -> ℝ := by
  apply Quotient.lift₂ (⟦· + ·⟧)
  intros
  apply Quotient.sound
  apply CauchySeq.add.spec <;> assumption

instance : Add ℝ := ⟨.add⟩

@[simp]
def Real.mk_add (a b: CauchySeq) : ⟦a⟧ + ⟦b⟧ = ⟦a + b⟧ := rfl
@[simp]
def CauchySeq.eval_add (a b: CauchySeq) (n: Nat) : (a + b) n = a n + b n := rfl

def CauchySeq.neg.spec (a b: CauchySeq) :
  a ≈ b ->
  is_cauchy_equiv (fun n => -a n) (fun n => -b n) := by
  intro ab ε ε_pos
  have ⟨δ, h⟩ := ab _ ε_pos
  refine ⟨δ, ?_⟩
  intro n m δ_le_n δ_le_m
  simp
  rw [neg_sub_neg, abs_sub_comm]
  apply h <;> assumption

def CauchySeq.neg (a: CauchySeq) : CauchySeq where
  seq n := -a n
  is_cacuhy := by apply CauchySeq.neg.spec <;> rfl

instance : Neg CauchySeq := ⟨.neg⟩

def Real.neg : ℝ -> ℝ := by
  apply Quotient.lift (⟦-·⟧)
  intros
  apply Quotient.sound
  apply CauchySeq.neg.spec <;> assumption

instance : Neg ℝ := ⟨.neg⟩

@[simp]
def Real.mk_neg (a: CauchySeq) : -⟦a⟧ = ⟦-a⟧ := rfl
@[simp]
def CauchySeq.eval_neg (a: CauchySeq) (n: Nat) : (-a) n = -a n := rfl

def CauchySeq.sub.spec (a b c d: CauchySeq) :
  a ≈ c -> b ≈ d ->
  is_cauchy_equiv (fun n => a n - b n) (fun n => c n - d n) := by
  intro ac bd ε ε_pos
  have ⟨δ, h⟩ := CauchySeq.add.spec a (-b) c (-d) ac (neg.spec _ _ bd) ε ε_pos
  refine ⟨δ, ?_⟩
  intro n m δ_le_n δ_le_m
  simp
  rw [sub_eq_add_neg (a n), sub_eq_add_neg (c m)]
  exact h n m δ_le_n δ_le_m

def CauchySeq.sub (a b: CauchySeq) : CauchySeq where
  seq n := a n - b n
  is_cacuhy := by
    apply sub.spec <;> rfl

instance : Sub CauchySeq := ⟨.sub⟩

def Real.sub : ℝ -> ℝ -> ℝ := by
  apply Quotient.lift₂ (⟦· - ·⟧)
  intros
  apply Quotient.sound
  apply CauchySeq.sub.spec <;> assumption

instance : Sub ℝ := ⟨.sub⟩

@[simp]
def Real.mk_sub (a b: CauchySeq) : ⟦a⟧ - ⟦b⟧ = ⟦a - b⟧ := rfl
@[simp]
def CauchySeq.eval_sub (a b: CauchySeq) (n: Nat) : (a - b) n = a n - b n := rfl

def CauchySeq.abs.proof1 (a b: Rat) :
  0 ≤ a -> b ≤ 0 -> ‖a - b‖ < ε -> ‖a + b‖ < ε := by
  intro ha hb habs
  cases lt_or_eq_of_le hb <;> rename_i hb
  · apply lt_of_le_of_lt _ habs
    rw [Rat.abs_def (a - b)]
    have : b < a := lt_of_lt_of_le hb ha
    have : 0 ≤ a - b := by
      apply Rat.add_le_add_right.mpr
      rw [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero, zero_add]
      apply le_of_lt; assumption
    rw [if_pos this]
    rw [Rat.abs_def, sub_eq_add_neg]
    split
    apply Rat.add_le_add_left.mp
    exact Rat.le_neg_of_nonpos b (le_of_lt hb)
    rw [neg_add_rev, add_comm]
    apply Rat.add_le_add_right.mp
    exact Rat.neg_le_of_nonneg a ha
  · subst b
    rw [sub_zero] at habs
    rwa [add_zero]

def CauchySeq.abs.spec (a b: CauchySeq) : a ≈ b ->
  is_cauchy_equiv (fun n => ‖a n‖) (fun n => ‖b n‖) := by
  intro ab ε ε_pos
  dsimp
  replace ⟨δ, ab⟩ := ab _ (Rat.half_pos ε_pos)
  refine ⟨δ, ?_⟩
  intro n m δ_le_n δ_le_m
  rw [Rat.abs_def (a n), Rat.abs_def (b m)]
  suffices ‖a.seq n - b.seq m‖ < ε by
    split <;> split <;> rename_i h g
    · exact this
    · rw [sub_eq_add_neg, neg_neg]
      apply CauchySeq.abs.proof1
      assumption
      rw [not_le] at g
      apply le_of_lt; assumption
      exact this
    · rw [sub_eq_add_neg]
      apply CauchySeq.abs.proof1
      apply Rat.neg_le_neg_iff.mpr
      rw [neg_neg]
      rw [not_le] at h
      apply le_of_lt; assumption
      apply Rat.neg_le_neg_iff.mpr
      rw [neg_neg]
      assumption
      rw [neg_sub_neg, abs_sub_comm]
      apply_assumption
    · rw [neg_sub_neg, abs_sub_comm]
      assumption
  replace ab  := ab _ _ δ_le_n δ_le_m
  apply lt_trans ab
  apply Rat.add_lt_add_right.mpr
  rw [add_neg_cancel]
  rw [←sub_eq_add_neg, Rat.sub_half]
  exact Rat.half_pos ε_pos

def CauchySeq.abs (a: CauchySeq) : CauchySeq where
  seq n := ‖a n‖
  is_cacuhy := by
    apply CauchySeq.abs.spec
    rfl

instance : AbsoluteValue CauchySeq CauchySeq where
  abs := .abs

def Real.abs : ℝ -> ℝ := by
  apply Quotient.lift (⟦‖·‖⟧)
  intros
  apply Quotient.sound
  apply CauchySeq.abs.spec
  assumption

instance : AbsoluteValue ℝ ℝ where
  abs := .abs

def CauchySeq.mul.spec (a b c d: CauchySeq) : a ≈ c -> b ≈ d ->
  is_cauchy_equiv (fun n => a n * b n) (fun n => c n * d n) := by
  intro ac bd ε ε_pos
  simp
  have ⟨amax,one_lt_amax,amax_spec⟩ := ‖a‖.upper_bound_with 1
  have ⟨dmax,one_lt_dmax,dmax_spec⟩ := ‖d‖.upper_bound_with 1

  have amax_pos : 0 < amax := lt_of_lt_of_le (by decide) one_lt_amax
  have dmax_pos : 0 < dmax := lt_of_lt_of_le (by decide) one_lt_dmax

  have amax_nonzero := (ne_of_lt amax_pos).symm
  have dmax_nonzero := (ne_of_lt dmax_pos).symm

  let ε₀ := (ε /? 2) /? dmax
  let ε₁ := (ε /? 2) /? amax

  have ε₀_pos : 0 < ε₀ := by
    apply div?_pos
    apply div?_pos
    assumption
    decide
    assumption
  have ε₁_pos : 0 < ε₁ := by
    apply div?_pos
    apply div?_pos
    assumption
    decide
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
  apply Rat.abs_add_le_add_abs
  rw [Rat.abs_mul, Rat.abs_mul]
  apply lt_of_le_of_lt (b := amax * _ + _ * dmax)
  apply Rat.add_le_add
  apply Rat.mul_le_mul_of_right_nonneg
  apply Rat.abs_nonneg
  apply le_of_lt
  apply amax_spec
  apply Rat.mul_le_mul_of_left_nonneg
  apply Rat.abs_nonneg
  apply le_of_lt
  apply dmax_spec
  apply lt_of_lt_of_le
  apply Rat.add_lt_add_of_lt_of_le
  apply (Rat.lt_iff_mul_left_pos _).mp
  assumption
  apply lt_of_lt_of_le _ one_lt_amax
  decide
  apply (Rat.le_iff_mul_right_pos _).mp
  apply le_of_lt
  assumption
  assumption
  rw [div?_mul_cancel, mul_div?_cancel, add_half]

def CauchySeq.mul (a b: CauchySeq) : CauchySeq where
  seq n := a n * b n
  is_cacuhy := by apply CauchySeq.mul.spec <;> rfl

instance : Mul CauchySeq := ⟨.mul⟩

def Real.mul : ℝ -> ℝ -> ℝ := by
  apply Quotient.lift₂ (⟦· * ·⟧)
  intros
  apply Quotient.sound
  apply CauchySeq.mul.spec <;> assumption

instance : Mul ℝ := ⟨.mul⟩

@[simp]
def Real.mk_mul (a b: CauchySeq) : ⟦a⟧ * ⟦b⟧ = ⟦a * b⟧ := rfl
@[simp]
def Real.eval_mul (a b: CauchySeq) (n: Nat) : (a * b) n = a n * b n := rfl

def CauchySeq.pow.spec (a b: CauchySeq) (n: ℕ) : a ≈ b ->
  is_cauchy_equiv (fun i => a i ^ n) (fun i => b i ^ n) := by
  intro eq
  induction n generalizing a b with
  | zero =>
    conv => { arg 1; intro x; rw [npow_zero] }
    conv => { arg 2; intro x; rw [npow_zero] }
    intro ε ε_pos
    exists 0
    intro n m hn hm
    simp [sub_self]
    assumption
  | succ n ih =>
    conv => { arg 1; intro x; rw [npow_succ] }
    conv => { arg 2; intro x; rw [npow_succ] }
    apply CauchySeq.mul.spec
      ⟨fun i => a i ^ n, ih _ _ (CauchySeq.refl _)⟩
      a
      ⟨fun i => b i ^ n, ih _ _ (CauchySeq.refl _)⟩
      b
    apply ih
    assumption
    assumption

instance : Pow CauchySeq ℕ where
  pow a n := {
    seq i := a i ^ n
    is_cacuhy := by
      apply CauchySeq.pow.spec
      rfl
  }

namespace Real

instance : SMul ℕ ℝ where
  smul a b := a * b
instance : SMul ℤ ℝ where
  smul a b := a * b
instance : Pow ℝ ℕ where
  pow := flip <| by
    intro n
    apply Quotient.lift (⟦· ^ n⟧)
    intro a b eq
    apply Quotient.sound
    apply CauchySeq.pow.spec
    assumption

-- we implement Ring here to get all the conveniences of it
-- and will implement IsField after we have defined division
-- in Math.Data.Real.Div
instance : IsRing ℝ where
  add_comm a b := by
    cases a, b
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro n
    apply add_comm
  add_assoc a b c := by
    cases a, b, c
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro n
    apply add_assoc
  mul_assoc a b c := by
    cases a, b, c
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro n
    apply mul_assoc
  zero_add a := by
    cases a
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro n
    apply zero_add
  add_zero a := by
    cases a
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro n
    apply add_zero
  zero_mul a := by
    cases a
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro n
    apply zero_mul
  mul_zero a := by
    cases a
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro n
    apply mul_zero
  one_mul a := by
    cases a
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro n
    apply one_mul
  mul_one a := by
    cases a
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro n
    apply mul_one
  left_distrib a b c := by
    cases a, b, c
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro n
    apply mul_add
  right_distrib a b c := by
    cases a, b, c
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro n
    apply add_mul
  sub_eq_add_neg a b := by
    cases a, b
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro n
    apply sub_eq_add_neg
  zero_nsmul a := by
    cases a
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro n
    apply zero_nsmul
  succ_nsmul n a := by
    cases a
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro n
    apply succ_nsmul
  npow_zero a := by
    cases a
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro n
    apply npow_zero
  npow_succ n a := by
    cases a
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro n
    apply npow_succ
  zsmul_ofNat n a := by
    cases a
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro n
    apply zsmul_ofNat
  zsmul_negSucc n a := by
    cases a
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro n
    apply zsmul_negSucc
  natCast_zero := rfl
  natCast_succ n := by
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro n
    apply natCast_succ
  neg_add_cancel a := by
    cases a
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro n
    apply neg_add_cancel
  intCast_ofNat n := by
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro n
    apply intCast_ofNat
  intCast_negSucc n := by
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro n
    apply intCast_negSucc
  ofNat_eq_natCast _ := rfl

instance : IsCommMagma ℝ where
  mul_comm a b := by
    cases a, b
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro n
    apply mul_comm

instance : IsSemiring ℝ := inferInstance

def ofRatHom : ℚ ↪+* ℝ where
  toFun := ofRat
  resp_zero := rfl
  resp_one := rfl
  resp_add := rfl
  resp_mul := rfl
  inj' := by
    suffices ∀a b: ℚ, ofRat a = ofRat b -> ¬a < b by
      intro a b eq
      apply Relation.eq_of_not_lt_or_gt (· < ·)
      apply this
      assumption
      apply this; symm
      assumption
    intro a b eq h
    have ⟨k, spec⟩ := Quotient.exact eq (b - a) ?_
    have : ‖a - b‖ < b - a := spec k k (le_refl _) (le_refl _)
    rw [Rat.abs_def, if_neg, neg_sub] at this
    exact lt_irrefl this
    rw [not_le, ←Rat.lt_add_iff_sub_lt, zero_add]
    assumption
    rw [←Rat.add_lt_iff_lt_sub, zero_add]
    assumption

instance : HasChar ℝ 0 := HasChar.of_ring_emb ofRatHom

def eq_iff_add_right {a b k: ℝ} : a = b ↔ a + k = b + k := by
  induction a, b, k using ind₃ with | mk a b k =>
  apply Iff.intro
  intro h
  rw [h]
  intro h
  apply Quotient.sound
  simp at h
  intro ε ε_pos
  replace ⟨δ, h⟩ := (Quotient.exact h _ (Rat.half_pos ε_pos)).merge (k.is_cacuhy _ (Rat.half_pos ε_pos))
  refine ⟨δ, ?_⟩
  intro n m δn δm
  replace h := h _ _ δn δm
  simp at h
  rw [sub_eq_add_neg, neg_add_rev, add_comm (-_) (-_), add_assoc,
    ←add_assoc (k n), add_comm (k n), add_assoc, ←add_assoc] at h
  rw [←add_zero (_ - _), ←add_neg_cancel (k n - k m), ←add_assoc]
  apply lt_of_le_of_lt
  apply Rat.abs_add_le_add_abs
  rw [←sub_eq_add_neg, ←sub_eq_add_neg] at h
  rw [neg_abs, ←add_half ε]
  apply Rat.add_lt_add
  exact h.left
  exact h.right

def eq_iff_add_left {a b k: ℝ} : a = b ↔ k + a = k + b := by
  rw [add_comm k, add_comm k]
  exact eq_iff_add_right

def eq_iff_sub_right {a b k: ℝ} : a = b ↔ a - k = b - k := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact eq_iff_add_right

def eq_iff_sub_left {a b k: ℝ} : a = b ↔ k - a = k - b := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact neg_inj.symm.trans eq_iff_add_left

def non_zero_of_ofNat (n: Nat) : (OfNat.ofNat (α := ℝ) n.succ) ≠ 0 := by
  intro h
  have ⟨δ, prf⟩ := (Quotient.exact h) (1 /? 2) (by decide)
  have : ‖(n.succ: ℚ) - 0‖ < 1 /? 2 := prf _ _ (le_refl _) (le_refl _)
  simp at this
  rw [Rat.abs_of_nonneg] at this
  have two_eq : (2: ℚ) = (2: ℕ) := rfl
  rw [Rat.lt_div_iff_mul_lt_of_pos, two_eq, ←natCast_mul] at this
  replace this := Rat.natCast_lt_natCast.mp this
  contradiction
  decide
  apply Rat.natCast_le_natCast.mpr
  apply Nat.zero_le

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply non_zero_of_ofNat)

instance : IsNontrivial ℝ where
  exists_ne := ⟨0, 1, by
    intro h
    replace h := Quotient.exact h
    replace ⟨k, h⟩ := h  (1 /? 2) (by decide)
    replace h: ‖0 - (1: ℚ)‖ < 1 /? (2: ℚ) := h k k (le_refl _) (le_refl _)
    dsimp at h
    contradiction⟩

end Real

namespace Real

scoped notation "⟦" v "⟧" => Real.mk v

end Real

-- def CauchySeq.ofIncreasingBounded
--   (f: Nat -> ℚ)
--   (inc: ∀n, f n ≤ f (n + 1))
--   (bounded: ∃B, ∀n, f n ≤ B) : CauchySeq where
--   seq := f
--   is_cacuhy := by
--     intro ε ε_pos
--     obtain ⟨B, bounded⟩ := bounded
--     have mono : Monotone f := by
--       intro x y h
--       induction y generalizing x with
--       | zero =>
--         cases Nat.le_zero.mp h
--         rfl
--       | succ y ih =>
--         cases lt_or_eq_of_le h
--         apply flip le_trans
--         apply inc
--         apply ih
--         apply Nat.le_of_lt_succ
--         assumption
--         subst x; rfl
--     apply Classical.byContradiction
--     intro h
--     unfold Eventually₂ at h
--     conv at h => {
--       rw [not_exists]; intro k
--       rw [Classical.not_forall]
--       arg 1; intro n
--       rw [Classical.not_forall]
--       arg 1; intro m
--       rw [not_imp, not_imp]
--       dsimp
--       rw [←le_iff_not_lt]
--     }
--     replace h := h 0
--     obtain ⟨n, m, hn, hm, h⟩ := h; clear hn hm
--     rcases le_total n m with n_le_m | m_le_n
--     have := mono n_le_m

--     repeat sorry
