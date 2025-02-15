import Math.Data.Rat.Order
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
    rw [←Rat.add_zero (c.max_until δ)]
    apply Rat.add_lt_add_of_le_of_lt
    rfl
    decide
  else
    suffices c δ + ‖c n - c δ‖ < max + 1 by
      apply lt_of_le_of_lt _ this
      rw [Rat.abs_def]
      split <;> rename_i g
      apply le_trans
      show c n ≤ c δ
      apply Rat.add_le_add_right.mpr
      rw [Rat.add_neg_self (c δ), ←Rat.sub_eq_add_neg]
      apply le_of_lt; assumption
      conv => { lhs; rw [←Rat.add_zero (c δ)] }
      apply Rat.add_le_add
      rfl
      apply Rat.neg_le_neg_iff.mpr
      rw [Rat.neg_neg]
      apply le_of_lt; assumption
      rw [Rat.sub_eq_add_neg, ←Rat.add_assoc, Rat.add_comm (c δ),
        Rat.add_assoc, Rat.add_neg_self, Rat.add_zero]
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

def Rat.half_pos {ε: ℚ} : 0 < ε -> 0 < ε /? 2 := (Rat.div_pos · (by decide))

@[refl]
def CauchySeq.Equiv.refl (a: CauchySeq) : Equiv a a := a.is_cacuhy
@[symm]
def CauchySeq.Equiv.symm {a b: CauchySeq} : Equiv a b -> Equiv b a := by
  intro h ε ε_pos
  replace ⟨δ, h⟩ := h ε ε_pos
  exists δ
  intro n m _ _
  rw [Rat.abs_sub_comm]
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
  rw [←Rat.mul_two, Rat.mul_div_cancel, ←Rat.mul_two, Rat.mul_div_cancel,
    Rat.abs_sub_comm (b n) (b m)] at this
  apply lt_of_le_of_lt _ this
  apply flip le_trans
  apply Rat.add_le_add
  rfl
  apply Rat.abs_add_le_add_abs
  apply flip le_trans
  apply Rat.abs_add_le_add_abs
  iterate 4 rw [Rat.sub_eq_add_neg]
  have : a n + -b m + (b n + -c m + (b m + -b n)) =
    a n + -c m + (-b m + b m) + (b n + -b n) := by ac_rfl
  rw [this]; clear this
  rw [Rat.neg_self_add, Rat.add_neg_self, Rat.add_zero, Rat.add_zero]

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
    rw [Rat.sub_self]
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
instance : OfNat CauchySeq n := ⟨.ofRat (OfNat.ofNat n: ℚ)⟩
instance : OfNat ℝ n := ⟨⟦OfNat.ofNat n⟧⟩

instance : Nonempty ℝ := ⟨0⟩

def CauchySeq.add.spec (a b c d: CauchySeq) :
  a ≈ c -> b ≈ d ->
  is_cauchy_equiv (fun n => a n + b n) (fun n => c n + d n) := by
  intro ac bd ε ε_pos
  have ⟨δ, h⟩ := (ac _ (Rat.half_pos ε_pos)).merge (bd _ (Rat.half_pos ε_pos))
  refine ⟨δ, ?_⟩
  intro n m δ_le_n δ_le_m
  show ‖a n + b n - (c m + d m)‖ < ε
  rw [Rat.sub_eq_add_neg, Rat.neg_add]
  have : ‖a n + b n + (-c m + -d m)‖ =
    ‖a n + -c m + (b n + -d m)‖ := by ac_rfl
  rw [this]; clear this
  replace ⟨ab, cd⟩  := h n m δ_le_n δ_le_m
  have := Rat.add_lt_add ab cd
  rw [←Rat.mul_two, Rat.mul_div_cancel] at this
  apply lt_of_le_of_lt _ this
  rw [←Rat.sub_eq_add_neg, ←Rat.sub_eq_add_neg]
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
  rw [Rat.neg_sub_neg, Rat.abs_sub_comm]
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
  rw [Rat.sub_eq_add_neg (a n), Rat.sub_eq_add_neg (c m)]
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
      rw [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.neg_self_add, Rat.add_zero, Rat.zero_add]
      apply le_of_lt; assumption
    rw [if_neg (not_lt_of_le this)]
    rw [Rat.abs_def]
    split
    rw [Rat.neg_add, Rat.sub_eq_add_neg]
    apply Rat.add_le_add_right.mp
    apply Rat.neg_le_self_of_nonneg
    assumption
    rw [Rat.sub_eq_add_neg]
    apply Rat.add_le_add_left.mp
    apply Rat.self_le_neg_of_nonpos
    assumption
  · subst b
    rw [Rat.sub_zero] at habs
    rwa [Rat.add_zero]

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
    · rw [Rat.neg_sub_neg, Rat.abs_sub_comm]
      exact this
    · rw [Rat.sub_eq_add_neg]
      apply CauchySeq.abs.proof1
      apply Rat.neg_le_neg_iff.mpr
      rw [Rat.neg_neg]
      apply le_of_lt; assumption
      apply Rat.neg_le_neg_iff.mpr
      rw [Rat.neg_neg]
      apply le_of_not_lt; assumption
      rw [Rat.neg_sub_neg, Rat.abs_sub_comm]
      exact this
    · rw [Rat.sub_eq_add_neg, Rat.neg_neg]
      apply CauchySeq.abs.proof1
      apply le_of_not_lt; assumption
      apply le_of_lt; assumption
      exact this
    · exact this
  replace ab  := ab _ _ δ_le_n δ_le_m
  apply lt_trans ab
  apply Rat.add_lt_add_right.mpr
  rw [Rat.add_neg_self]
  conv => {
    rhs; lhs;
    rw [←Rat.mul_div_cancel 2 ε (by decide)]
  }
  rw [Rat.mul_two, Rat.add_assoc, Rat.add_neg_self, Rat.add_zero, Rat.div_eq_mul_inv]
  apply Rat.div_pos
  assumption
  decide

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
    apply Rat.div_pos
    apply Rat.div_pos
    assumption
    decide
    assumption
  have ε₁_pos : 0 < ε₁ := by
    apply Rat.div_pos
    apply Rat.div_pos
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
  rw [←Rat.add_zero (_ - _), ←Rat.add_neg_self (a n * d m),
    Rat.sub_eq_add_neg]
  have :
    a n * b n + -(c m * d m) + (a n * d m + -(a n * d m)) =
    a n * b n + -(a n * d m) + (a n * d m + -(c m * d m)) := by ac_rfl
  rw [this]; clear this
  iterate 2 rw [←Rat.sub_eq_add_neg]
  rw [←Rat.mul_sub, ←Rat.sub_mul]
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
  apply Rat.mul_lt_mul_of_left_pos
  apply lt_of_lt_of_le _ one_lt_amax
  decide
  assumption
  apply Rat.mul_le_mul_of_right_nonneg
  apply le_trans _ one_lt_dmax
  decide
  apply le_of_lt; assumption
  rw [Rat.mul_div_cancel, Rat.mul_comm, Rat.mul_div_cancel,
    ←Rat.mul_two, Rat.mul_div_cancel]

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

namespace Real

def sub_eq_add_neg (a b: ℝ) : a - b = a + -b := by
  induction a, b using ind₂ with | mk a b =>
  simp
  apply Quotient.sound
  apply CauchySeq.pointwise
  intro n
  simp
  rw [Rat.sub_eq_add_neg]

def add_comm (a b: ℝ) : a + b = b + a := by
  induction a, b using ind₂ with | mk a b =>
  simp
  apply Quotient.sound
  apply CauchySeq.pointwise
  intro n
  simp
  rw [Rat.add_comm]

def add_assoc (a b c: ℝ) : a + b + c = a + (b + c) := by
  induction a, b, c using ind₃ with | mk a b =>
  simp
  apply Quotient.sound
  apply CauchySeq.pointwise
  intro n
  simp
  rw [Rat.add_assoc]

def add_neg_self (a: ℝ) : a + -a = 0 := by
  induction a using ind with | mk a =>
  apply Quotient.sound
  apply CauchySeq.pointwise
  intro n
  simp
  rw [Rat.add_neg_self]
  rfl

def neg_self_add (a: ℝ) : -a + a = 0 := by
  induction a using ind with | mk a =>
  apply Quotient.sound
  apply CauchySeq.pointwise
  intro n
  simp
  rw [Rat.neg_self_add]
  rfl

def sub_self (a: ℝ) : a - a = 0 := by
  induction a using ind with | mk a =>
  apply Quotient.sound
  apply CauchySeq.pointwise
  intro n
  simp
  rw [Rat.sub_self]
  rfl

instance : @Std.Commutative ℝ (· + ·) := ⟨add_comm⟩
instance : @Std.Associative ℝ (· + ·) := ⟨add_assoc⟩

def mul_comm (a b: ℝ) : a * b = b * a := by
  induction a, b using ind₂ with | mk a b =>
  apply Quotient.sound
  apply CauchySeq.pointwise
  intro n
  simp
  rw [Rat.mul_comm]

def mul_assoc (a b c: ℝ) : a * b * c = a * (b * c) := by
  induction a, b, c using ind₃ with | mk a b c =>
  apply Quotient.sound
  apply CauchySeq.pointwise
  intro n
  simp
  rw [Rat.mul_assoc]

instance : @Std.Commutative ℝ (· * ·) := ⟨mul_comm⟩
instance : @Std.Associative ℝ (· * ·) := ⟨mul_assoc⟩

def neg_add (a b: ℝ) : -(a + b) = -a + -b := by
  induction a, b using ind₂ with | mk a b =>
  apply Quotient.sound
  apply CauchySeq.pointwise
  intro n
  simp
  rw [Rat.neg_add]

def neg_sub (a b: ℝ) : -(a - b) = b - a := by
  induction a, b using ind₂ with | mk a b =>
  apply Quotient.sound
  apply CauchySeq.pointwise
  intro n
  simp
  rw [Rat.neg_sub]

def neg_sub_neg (a b: ℝ) : -a - -b = b - a := by
  induction a, b using ind₂ with | mk a b =>
  apply Quotient.sound
  apply CauchySeq.pointwise
  intro n
  simp
  rw [Rat.neg_sub_neg]

def neg_mul_left (a b: ℝ) : -(a * b) = -a * b := by
  induction a, b using ind₂ with | mk a b =>
  apply Quotient.sound
  apply CauchySeq.pointwise
  intro n
  simp
  rw [Rat.neg_mul_left]

def neg_mul_right (a b: ℝ) : -(a * b) = a * -b := by
  induction a, b using ind₂ with | mk a b =>
  apply Quotient.sound
  apply CauchySeq.pointwise
  intro n
  simp
  rw [Rat.neg_mul_right]

@[simp]
def neg_neg (a: ℝ) : - -a = a := by
  induction a using ind with | mk a =>
  apply Quotient.sound
  apply CauchySeq.pointwise
  intro n
  simp

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
  rw [Rat.sub_eq_add_neg, Rat.neg_add, Rat.add_assoc,
    ←Rat.add_assoc (k n), Rat.add_comm (k n), Rat.add_assoc, ←Rat.add_assoc] at h
  rw [←Rat.add_zero (_ - _), ←Rat.add_neg_self (k n - k m), ←Rat.add_assoc]
  apply lt_of_le_of_lt
  apply Rat.abs_add_le_add_abs
  rw [←Rat.sub_eq_add_neg, ←Rat.sub_eq_add_neg] at h
  rw [Rat.abs_neg, Rat.add_half ε]
  apply Rat.add_lt_add
  exact h.left
  exact h.right

def eq_iff_neg_eq {a b: ℝ} : a = b ↔ -a = -b := by
  apply Iff.intro
  intro h; rw [h]
  intro h
  have : a + -a = b + -b := by rw [add_neg_self, add_neg_self]
  rw [h] at this
  exact eq_iff_add_right.mpr this

def eq_iff_add_left {a b k: ℝ} : a = b ↔ k + a = k + b := by
  rw [add_comm k, add_comm k]
  exact eq_iff_add_right

def eq_iff_sub_right {a b k: ℝ} : a = b ↔ a - k = b - k := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact eq_iff_add_right

def eq_iff_sub_left {a b k: ℝ} : a = b ↔ k - a = k - b := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact eq_iff_neg_eq.trans eq_iff_add_left

def add_zero (a: ℝ) : a + 0 = a := by
  induction a using ind with | mk a =>
  apply Quotient.sound
  apply CauchySeq.pointwise
  intro; simp
  erw [Rat.add_zero]

def zero_add (a: ℝ) : 0 + a = a := by
  rw [add_comm, add_zero]

def mul_zero (a: ℝ) : a * 0 = 0 := by
  induction a using ind with | mk a =>
  apply Quotient.sound
  apply CauchySeq.pointwise
  intro; simp
  erw [Rat.mul_zero]
  rfl

def zero_mul (a: ℝ) : 0 * a = 0 := by
  rw [mul_comm, mul_zero]

def mul_one (a: ℝ) : a * 1 = a := by
  induction a using ind with | mk a =>
  apply Quotient.sound
  apply CauchySeq.pointwise
  intro; simp
  erw [Rat.mul_one]

def one_mul (a: ℝ) : 1 * a = a := by
  rw [mul_comm, mul_one]

def sub_add_cancel (a b: ℝ) : a - b + b = a := by
  rw [sub_eq_add_neg, add_assoc, neg_self_add, add_zero]

def eq_of_sub_eq_zero {a b: ℝ} : a - b = 0 -> a = b := by
  intro h
  have : a = (a - b) + b := by rw [sub_add_cancel]
  rw [h, zero_add] at this
  exact this

def add_mul (a b k: ℝ) : (a + b) * k = a * k + b * k := by
  induction a, b, k using ind₃ with | mk a b k =>
  apply Quotient.sound
  apply CauchySeq.pointwise
  intro; simp
  erw [Rat.add_mul]

def mul_add (a b k: ℝ) : k * (a + b) = k * a + k * b := by
  iterate 3 rw [mul_comm k]
  rw [add_mul]

def sub_mul (a b k: ℝ) : (a - b) * k = a * k - b * k := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_mul, neg_mul_left]

def mul_sub (a b k: ℝ) : k * (a - b) = k * a - k * b := by
  iterate 3 rw [mul_comm k]
  rw [sub_mul]

def non_zero_of_ofNat (n: Nat) : (OfNat.ofNat (α := ℝ) n.succ) ≠ 0 := by
  intro h
  have ⟨δ, prf⟩ := (Quotient.exact h) (1 /? 2) (by decide)
  have : ‖Rat.ofNat n.succ - 0‖ < 1 /? 2 := prf _ _ (le_refl _) (le_refl _)
  simp at this
  rw [Rat.sub_zero] at this
  contradiction

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply non_zero_of_ofNat)

def sub_zero (a: ℝ) : a - 0 = a := by
  induction a using ind with | mk a =>
  apply Quotient.sound
  apply CauchySeq.pointwise
  intro n
  simp
  erw [Rat.sub_zero]

def zero_sub (a: ℝ) : 0 - a = -a := by
  induction a using ind with | mk a =>
  apply Quotient.sound
  apply CauchySeq.pointwise
  intro n
  simp
  erw [Rat.zero_sub]

def two_mul (a: ℝ) : 2 * a = a + a := by
  have : (2: ℝ) = 1 + 1 := by
    apply Quotient.sound
    apply CauchySeq.pointwise
    intro
    show 2 = 1 + 1
    rfl
  rw [this, add_mul, one_mul]

instance : NatCast ℝ where
  natCast n := ⟦CauchySeq.ofRat (Rat.ofNat n)⟧
instance : IntCast ℝ where
  intCast n := ⟦CauchySeq.ofRat (Rat.ofInt n)⟧

def neg_inj {a b: ℝ} : -a = -b ↔ a = b := by
  apply flip Iff.intro
  intro h; rw [h]
  intro h
  rw [←neg_neg a, ←neg_neg b, h]

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

def CauchySeq.ofIncreasingBounded
  (f: Nat -> ℚ)
  (inc: ∀n, f n ≤ f (n + 1))
  (bounded: ∃B, ∀n, f n ≤ B) : CauchySeq where
  seq := f
  is_cacuhy := by
    intro ε ε_pos
    obtain ⟨B, bounded⟩ := bounded
    have mono : Monotone f := by
      intro x y h
      induction y generalizing x with
      | zero =>
        cases Nat.le_zero.mp h
        rfl
      | succ y ih =>
        cases lt_or_eq_of_le h
        apply flip le_trans
        apply inc
        apply ih
        apply Nat.le_of_lt_succ
        assumption
        subst x; rfl
    apply Classical.byContradiction
    intro h
    unfold Eventually₂ at h
    conv at h => {
      rw [not_exists]; intro k
      rw [Classical.not_forall]
      arg 1; intro n
      rw [Classical.not_forall]
      arg 1; intro m
      rw [not_imp, not_imp]
      dsimp
      rw [←le_iff_not_lt]
    }
    replace h := h 0
    obtain ⟨n, m, hn, hm, h⟩ := h; clear hn hm
    rcases le_total n m with n_le_m | m_le_n
    have := mono n_le_m

    repeat sorry
