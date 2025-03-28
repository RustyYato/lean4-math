import Math.Data.Real.Basic
import Math.Data.Set.Order.Bounds

namespace CauchySeq

def IsPos (a: CauchySeq): Prop := ∃B, 0 < B ∧ Eventually fun n => B ≤ a n

def IsPos.spec (a b: CauchySeq) : a ≈ b -> a.IsPos -> b.IsPos := by
  intro ab pos
  replace ⟨B, B_pos, pos⟩ := pos
  refine ⟨_, Rat.half_pos B_pos, ?_⟩
  obtain ⟨K, prf⟩ := pos
  replace ⟨δ, ab⟩ := ab _ (Rat.half_pos B_pos)
  simp at ab prf
  refine ⟨max K δ, ?_⟩
  intro n Kδ_le_n
  apply le_trans _ (Rat.sub_abs_self_sub (a n) (b n))
  apply flip le_trans
  apply Rat.sub_le_sub
  apply prf
  apply (max_le_iff.mp Kδ_le_n).left
  apply le_of_lt;
  apply ab
  iterate 2 apply (max_le_iff.mp Kδ_le_n).right
  conv => {
    rhs; lhs; rw [←mul_div?_cancel B 2 (by decide)]
  }
  rw [two_mul, add_sub_assoc, add_sub_cancel]

def non_zero_of_IsPos (a: CauchySeq) : a.IsPos -> ¬a ≈ 0 := by
  intro pos eq_zero
  obtain ⟨B, B_pos, pos⟩ := pos
  replace ⟨δ, prf⟩  := pos.to₂_right.merge (eq_zero _ B_pos)
  replace ⟨pos, eq_zero⟩ := prf δ δ (le_refl _) (le_refl _)
  clear prf
  erw [sub_zero] at eq_zero
  rw [Rat.abs_def] at eq_zero
  split at eq_zero <;> rename_i h
  exact lt_irrefl <| lt_of_lt_of_le eq_zero pos
  rw [not_le] at h
  exact lt_asymm B_pos (lt_of_le_of_lt pos h)

def abs_pos_of_non_zero {f : CauchySeq} (hf : ¬f ≈ 0) : IsPos |f| := by
  false_or_by_contra
  rename_i nk

  refine hf fun ε ε_pos => ?_
  replace nk : ∀ (x : ℚ), 0 < x → ∀ (y : Nat), ∃ z, ∃ (_ : y ≤ z), |f z| < x := by
    intro x hx n
    have nk := not_exists.mp (not_and.mp (not_exists.mp nk x) hx) n
    have ⟨m,prf⟩ := Classical.not_forall.mp nk
    have ⟨hm,prf⟩ := Classical.not_imp.mp prf
    exists m
    exists hm
    apply lt_of_not_le
    assumption

  have ⟨i,hi⟩ := f.is_cacuhy _ (Rat.half_pos ε_pos)
  rcases nk _ (Rat.half_pos ε_pos) i with ⟨j, ij, hj⟩
  refine ⟨j, fun k _ jk _ => ?_⟩
  have : ∀y, seq 0 y = 0 := fun _ => rfl
  dsimp
  rw [this, sub_zero]
  have := lt_of_le_of_lt (Rat.abs_add_le_add_abs _ _) (Rat.add_lt_add (hi k j (le_trans ij jk) ij) hj)
  rwa [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero,
      ←mul_two, div?_mul_cancel] at this

def pos_or_neg_of_abs_pos {f : CauchySeq} (hf : IsPos |f|) : IsPos f ∨ IsPos (-f) := by
  obtain ⟨B, B_pos, pos⟩ := hf
  replace ⟨δ, prf⟩ := pos.to₂_right.merge (f.is_cacuhy _ (Rat.half_pos B_pos))
  replace ⟨pos, f_eqv⟩ := prf _ _  (le_refl _) (le_refl _)
  replace pos: B ≤ |f δ| := pos
  clear f_eqv
  rw [Rat.abs_def] at pos
  split at pos <;> rename_i h
  · clear h
    left
    refine ⟨_, Rat.half_pos B_pos, δ, ?_⟩
    intro n δ_n
    apply le_trans _ <| Rat.sub_abs_self_sub (f δ) (f n)
    apply flip le_trans
    apply Rat.sub_le_sub
    assumption
    apply le_of_lt
    simp at prf
    exact (prf δ n (le_refl _) δ_n).right
    rw [Rat.sub_half]
  · clear h
    right
    refine ⟨_, Rat.half_pos B_pos, δ, ?_⟩
    intro n δ_n
    apply le_trans _ <| Rat.sub_abs_self_sub (-f δ) (-f n)
    rw [neg_sub_neg]
    apply flip le_trans
    apply Rat.sub_le_sub
    assumption
    apply le_of_lt
    simp at prf
    exact (prf n δ δ_n (le_refl _)).right
    rw [Rat.sub_half]

def not_neg_of_pos {f: CauchySeq} : f.IsPos -> ¬(-f).IsPos := by
  intro pos neg
  obtain ⟨A, A_pos, pos⟩ := pos
  obtain ⟨B, B_pos, neg⟩ := neg
  have ⟨δ, prf⟩ := pos.merge neg
  have ⟨pos, neg⟩ := prf _ (le_refl _)
  have : - - f δ ≤ - B := Rat.neg_le_neg_iff.mp neg
  rw [neg_neg] at this
  have A_le_neg_B := le_trans pos this
  have := lt_of_lt_of_le A_pos A_le_neg_B
  have : - - B < 0 := Rat.neg_lt_neg_iff.mp this
  rw [neg_neg] at this
  exact lt_asymm B_pos this

def add_pos {a b: CauchySeq} : a.IsPos -> b.IsPos -> (a + b).IsPos := by
  intro apos bpos
  obtain ⟨A, A_pos, apos⟩ := apos
  obtain ⟨B, B_pos, bpos⟩ := bpos
  refine ⟨A + B, ?_, ?_⟩
  rw [←add_zero 0]
  apply Rat.add_lt_add
  assumption
  assumption
  have ⟨δ, prf⟩ := apos.merge bpos
  exists δ
  intro n δn
  replace prf := prf _ δn
  obtain ⟨apos, bpos⟩ := prf
  apply Rat.add_le_add <;> assumption

end CauchySeq

namespace Real

local instance : Coe ℚ ℝ := ⟨.ofRat⟩

def IsPos : ℝ -> Prop := by
  apply Quotient.lift CauchySeq.IsPos
  intro a b ab
  ext; apply Iff.intro
  apply CauchySeq.IsPos.spec; assumption
  apply CauchySeq.IsPos.spec; symm; assumption

@[simp]
def mk_IsPos (a: CauchySeq) : ⟦a⟧.IsPos = a.IsPos := rfl

def zero_not_pos : ¬IsPos 0 := by
  intro h
  exact CauchySeq.non_zero_of_IsPos _ h (by rfl)
def non_zero_of_IsPos {a: ℝ} : a.IsPos -> a ≠ 0 := by
  intro h g
  subst g
  exact zero_not_pos h

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply non_zero_of_IsPos <;> invert_tactic)

def abs_pos_of_non_zero {a: ℝ} : a ≠ 0 -> |a|.IsPos := by
  intro h
  induction a using ind with | mk a =>
  apply CauchySeq.abs_pos_of_non_zero
  intro g
  apply h
  apply Quotient.sound
  assumption

def pos_or_eq_or_neg (a: ℝ) : a.IsPos ∨ a = 0 ∨ (-a).IsPos := by
  by_cases h:a = 0
  right; left; assumption
  induction a using ind with | mk a =>
  cases CauchySeq.pos_or_neg_of_abs_pos (Real.abs_pos_of_non_zero h)
  left; assumption
  right; right; assumption

def not_neg_of_pos {a: ℝ} : a.IsPos -> ¬(-a).IsPos := by
  induction a using ind with | mk a =>
  apply CauchySeq.not_neg_of_pos

def add_pos {a b: ℝ} : a.IsPos -> b.IsPos -> (a + b).IsPos := by
  induction a, b using ind₂ with | mk a b =>
  apply CauchySeq.add_pos

instance : LT ℝ where
  lt a b := (b - a).IsPos
instance : LE ℝ where
  le a b := a < b ∨ a = b

def lt_def (a b: ℝ) : (a < b) = (b - a).IsPos := rfl
def le_def (a b: ℝ) : (a ≤ b) = (a < b ∨ a = b) := rfl

instance : LT CauchySeq where
  lt a b := (b - a).IsPos
instance : LE CauchySeq where
  le a b := a < b ∨ a ≈ b

def CauchySeq.lt_def (a b: CauchySeq) : (a < b) = (b - a).IsPos := rfl
def CauchySeq.le_def (a b: CauchySeq) : (a ≤ b) = (a < b ∨ a ≈ b) := rfl

instance : IsLinearOrder ℝ where
  lt_iff_le_and_not_le := by
    intro a b
    simp [lt_def, le_def]
    apply Iff.intro
    intro h
    repeat any_goals apply And.intro
    left; assumption
    intro g
    apply not_neg_of_pos h
    rw [neg_sub]
    assumption
    intro h
    subst h
    rw [sub_self] at h
    exact zero_not_pos h
    intro ⟨ab, nba⟩
    cases ab
    assumption
    subst b
    have := nba.right rfl
    contradiction
  le_antisymm := by
    intro a b ab ba
    cases ab <;> rename_i ab
    cases ba <;> rename_i ba
    have := not_neg_of_pos ab
    rw [neg_sub] at this
    contradiction
    symm; assumption
    assumption
  lt_or_le := by
    intro a b
    rcases pos_or_eq_or_neg (b - a) with ab | eq | ba
    left; assumption
    cases eq_of_sub_eq_zero eq
    right; right; rfl
    rw [neg_sub] at ba
    right; left; assumption
  le_trans := by
    intro a b c ab bc
    cases ab <;> rename_i ab
    cases bc <;> rename_i bc
    · replace ab : (b - a).IsPos := ab
      replace bc : (c - b).IsPos := bc
      left
      show (c - a).IsPos
      rw [←add_zero c, ←neg_add_cancel b, ←add_assoc, sub_eq_add_neg, add_assoc,
        ←sub_eq_add_neg, ←sub_eq_add_neg]
      apply add_pos <;> assumption
    subst c; left; assumption
    subst b; assumption

def lt_iff_neg_lt_neg {a b: ℝ} : a < b ↔ -b < -a := by
  revert a b
  suffices ∀{a b: ℝ}, a < b -> -b < -a by
    intro a b
    apply Iff.intro this
    intro h
    rw [←neg_neg a, ←neg_neg b]
    exact this h
  intro a b lt
  show IsPos _
  rw [neg_sub_neg]
  exact lt

def le_iff_neg_le_neg {a b: ℝ} : a ≤ b ↔ -b ≤ -a := by
  apply le_iff_of_lt_iff
  apply lt_iff_neg_lt_neg

def lt_iff_add_lt_add_right {a b k: ℝ} : a < b ↔ a + k < b + k := by
  show IsPos _ ↔ IsPos _
  rw [sub_eq_add_neg (b + k), neg_add_rev]
  have : b + k + (-k + -a) = b + -a + (k + -k) := by ac_rfl
  rw [this]; clear this
  rw [add_neg_cancel, add_zero, sub_eq_add_neg]

def lt_iff_add_lt_add_left {a b k: ℝ} : a < b ↔ k + a < k + b := by
  rw [add_comm k, add_comm k]
  apply lt_iff_add_lt_add_right

def le_iff_add_le_add_right {a b k: ℝ} : a ≤ b ↔ a + k ≤ b + k := by
  apply le_iff_of_lt_iff
  apply lt_iff_add_lt_add_right

def le_iff_add_le_add_left {a b k: ℝ} : a ≤ b ↔ k + a ≤ k + b := by
  apply le_iff_of_lt_iff
  apply lt_iff_add_lt_add_left

def lt_iff_sub_lt_sub_right {a b k: ℝ} : a < b ↔ a - k < b - k := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  apply lt_iff_add_lt_add_right

def le_iff_sub_le_sub_right {a b k: ℝ} : a ≤ b ↔ a - k ≤ b - k := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  apply le_iff_add_le_add_right

def lt_iff_sub_lt_sub_left {a b k: ℝ} : a < b ↔ k - b < k - a := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  apply Iff.trans _ lt_iff_add_lt_add_left
  apply lt_iff_neg_lt_neg

def le_iff_sub_le_sub_left {a b k: ℝ} : a ≤ b ↔ k - b ≤ k - a := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  apply Iff.trans _ le_iff_add_le_add_left
  apply le_iff_neg_le_neg

def mul_pos_of_pos_of_pos (a b: ℝ) : a.IsPos -> b.IsPos -> (a * b).IsPos := by
  intro apos bpos
  induction a, b using ind₂ with | mk a b =>
  obtain ⟨A, A_pos, apos⟩ := apos
  obtain ⟨B, B_pos, bpos⟩ := bpos
  show (a * b).IsPos
  have ⟨δ, prf⟩ := apos.merge bpos
  refine ⟨A * B, Rat.mul_pos A_pos B_pos, δ, ?_⟩
  intro n δn
  obtain ⟨apos, bpos⟩ := prf _ δn
  apply Rat.mul_le_mul_nonneg
  apply le_of_lt; assumption
  assumption
  apply le_of_lt; assumption
  assumption
def mul_pos_of_neg_of_neg (a b: ℝ) : (-a).IsPos -> (-b).IsPos -> (a * b).IsPos := by
  intro apos bpos
  have := mul_pos_of_pos_of_pos _ _ apos bpos
  rwa [←neg_mul_left, ←neg_mul_right, neg_neg] at this
def mul_neg_of_pos_of_neg (a b: ℝ) : a.IsPos -> (-b).IsPos -> (-(a * b)).IsPos := by
  intro apos bpos
  have := mul_pos_of_pos_of_pos _ _ apos bpos
  rwa [←neg_mul_right] at this
def mul_neg_of_neg_of_pos (a b: ℝ) : (-a).IsPos -> b.IsPos -> (-(a * b)).IsPos := by
  intro apos bpos
  have := mul_pos_of_pos_of_pos _ _ apos bpos
  rwa [←neg_mul_left] at this

open Classical in def abs_def (a: ℝ) : |a| = if 0 ≤ a then a else -a := by
  cases a with | mk a =>
  split
  rename_i h
  cases h <;> rename_i h
  replace h: IsPos (⟦a⟧ - 0) := h
  rw [sub_zero] at h
  replace ⟨B, Bpos, k, spec⟩ := h
  apply Quotient.sound
  apply CauchySeq.eventually_pointwise
  exists k
  intro n k_le_n
  show |_| = _
  rw [Rat.abs_def, if_pos]
  apply flip le_trans
  apply spec
  assumption
  apply le_of_lt; assumption
  rw [←h]
  rfl
  rename_i h
  replace h: IsPos (0 - ⟦a⟧) := lt_of_not_le h
  rw [zero_sub] at h
  replace ⟨B, Bpos, k, spec⟩ := h
  apply Quotient.sound
  apply CauchySeq.eventually_pointwise
  exists k
  intro n k_le_n
  show |_| = _
  rw [Rat.abs_def, if_neg]
  rfl
  rw [not_le]
  apply Rat.neg_lt_neg_iff.mpr
  apply flip lt_of_lt_of_le
  apply spec
  assumption
  assumption

def lt_sub_iff_add_lt (a b k: ℝ) :  a < b - k ↔ a + k < b := by
  show IsPos _ ↔ IsPos _
  rw [sub_eq_add_neg _ (a + k), neg_add_rev, ←add_assoc, ←sub_eq_add_neg, ←sub_eq_add_neg]

def sub_lt_iff_lt_add (a b k: ℝ) :  a - k < b ↔ a < b + k := by
  rw [sub_eq_add_neg]
  conv => { rhs; rw [←neg_neg k, ←sub_eq_add_neg] }
  symm
  apply lt_sub_iff_add_lt

def sub_le_iff_le_add (a b k: ℝ) :  a - k ≤ b ↔ a ≤ b + k := by
  apply le_iff_of_lt_iff
  apply lt_sub_iff_add_lt

def le_sub_iff_add_le (a b k: ℝ) :  a ≤ b - k ↔ a + k ≤ b := by
  apply le_iff_of_lt_iff
  apply sub_lt_iff_lt_add

def neg_lt_neg_iff (a b: ℝ) : -a < -b ↔ b < a := by
  show IsPos _ ↔ IsPos _
  rw [sub_eq_add_neg, neg_neg, add_comm, ←sub_eq_add_neg]

def neg_le_neg_iff (a b: ℝ) : -a ≤ -b ↔ b ≤ a := by
  apply le_iff_of_lt_iff
  apply neg_lt_neg_iff

def neg_zero : -(0: ℝ) = 0 := rfl

def abs_sub_comm (a b: ℝ) : |a - b| = |b - a| := by
  rw [abs_def, abs_def]
  split <;> rename_i h
  rcases lt_or_eq_of_le h with h | h
  · rw [if_neg, neg_sub]
    rw [←neg_le_neg_iff, neg_sub]
    apply not_le_of_lt
    assumption
  cases eq_of_sub_eq_zero h.symm
  rw [sub_self, if_pos (le_refl _)]
  rw [←lt_iff_not_le] at h
  rw [if_pos, neg_sub]
  rw [←neg_le_neg_iff, neg_sub]
  apply le_of_lt
  assumption

def square_nonneg (a: ℝ) : 0 ≤ a * a := by
  rcases pos_or_eq_or_neg a with p | eq | n
  have := mul_pos_of_pos_of_pos a a p p
  left
  show (a * a - 0).IsPos
  rw [sub_zero]
  assumption
  rw [eq, mul_zero]
  have := mul_pos_of_neg_of_neg a a n n
  left
  show (a * a - 0).IsPos
  rw [sub_zero]
  assumption

def eq_zero_of_square_eq_zero (a: ℝ) : a * a = 0 -> a = 0 := by
  intro h
  rcases pos_or_eq_or_neg a with p | eq | n
  have := mul_pos_of_pos_of_pos a a p p
  rw [h] at this
  have := zero_not_pos
  contradiction
  assumption
  have := mul_pos_of_neg_of_neg a a n n
  rw [h] at this
  have := zero_not_pos
  contradiction

def lt_iff_intCast_lt (a b: Int) : a < b ↔ (a: ℝ) < b := by
  apply Iff.intro
  · intro h
    exists b - a
    apply And.intro
    · apply Rat.add_lt_add_right.mpr
      show 0 + (a: ℚ) < _
      rw [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero, zero_add]
      exact Rat.intCast_lt_intCast.mpr h
    · exists 0
      intro n hn
      rfl
  · intro h
    replace h : (b - a: ℝ).IsPos := h
    obtain ⟨B, B_pos, k, spec⟩ := h
    replace spec : B ≤ b -a := spec k (le_refl _)
    replace spec := Rat.add_lt_add_of_lt_of_le B_pos spec
    rw [add_comm B] at spec
    replace spec := Rat.add_lt_add_right.mpr spec
    replace spec := Rat.add_lt_add_of_lt_of_le spec (le_refl _: (a: ℚ) ≤ a)
    rw [sub_eq_add_neg, add_assoc, neg_add_cancel, zero_add, add_zero] at spec
    exact Rat.intCast_lt_intCast.mp spec

def lt_iff_natCast_lt (a b: Nat) : a < b ↔ (a: ℝ) < b := by
  apply Iff.trans _ (lt_iff_intCast_lt a b)
  apply Int.ofNat_lt.symm

def le_iff_intCast_le (a b: Int) : a ≤ b ↔ (a: ℝ) ≤ b := by
  apply le_iff_of_lt_iff
  apply lt_iff_intCast_lt

def le_iff_natCast_le (a b: Nat) : a ≤ b ↔ (a: ℝ) ≤ b := by
  apply le_iff_of_lt_iff
  apply lt_iff_natCast_lt

def zero_lt_iff_pos {a: ℝ} : 0 < a ↔ a.IsPos :=by
  rw [lt_def, sub_zero]

def neg_nonpos_of_nonneg (a: ℝ) : 0 ≤ a -> -a ≤ 0 := by
  rw [←neg_le_neg_iff]
  exact id

def neg_nonneg_of_nonpos (a: ℝ) : a ≤ 0 -> 0 ≤ -a := by
  rw [←neg_le_neg_iff]
  exact id

def mul_nonneg_of_nonneg_of_nonneg (a b: ℝ) :
  0 ≤ a -> 0 ≤ b -> 0 ≤ a * b := by
  intro ha hb
  rcases Or.symm (lt_or_eq_of_le ha) with ha | ha
  subst a; rw [zero_mul]
  rcases Or.symm (lt_or_eq_of_le hb) with hb | hb
  subst b; rw [mul_zero]
  apply le_of_lt
  rw [zero_lt_iff_pos] at *
  exact mul_pos_of_pos_of_pos a b ha hb

def mul_nonneg_of_nonpos_of_nonpos (a b: ℝ) :
  a ≤ 0 -> b ≤ 0 -> 0 ≤ a * b := by
  intro ha hb
  rw [←neg_neg (a * b), neg_mul_left, neg_mul_right]
  apply mul_nonneg_of_nonneg_of_nonneg
  exact neg_nonneg_of_nonpos a ha
  exact neg_nonneg_of_nonpos b hb

def mul_lt_mul_of_pos_left {a b k: ℝ} : 0 < k -> a < b -> k * a < k * b := by
  intro hk ab
  rw [lt_def] at ab
  rw [zero_lt_iff_pos] at hk
  rw [lt_def, ←mul_sub]
  exact mul_pos_of_pos_of_pos k (b - a) hk ab

def mul_lt_mul_of_pos_right {a b k: ℝ} : 0 < k -> a < b -> a * k < b * k := by
  rw [mul_comm _ k, mul_comm _ k]
  apply mul_lt_mul_of_pos_left

def mul_le_mul_of_nonneg_left {a b k: ℝ} : 0 ≤ k -> a ≤ b -> k * a ≤ k * b := by
  intro hk ab
  rcases Or.symm (lt_or_eq_of_le hk) with hk | hk
  subst k; rw [zero_mul, zero_mul]
  rcases Or.symm (lt_or_eq_of_le ab) with ab | ab
  subst b; rfl
  apply le_of_lt
  apply mul_lt_mul_of_pos_left
  assumption
  assumption

def mul_le_mul_of_nonneg_right {a b k: ℝ} : 0 ≤ k -> a ≤ b -> a * k ≤ b * k := by
  rw [mul_comm _ k, mul_comm _ k]
  apply mul_le_mul_of_nonneg_left

def mul_lt_mul_of_nonneg {a b c d: ℝ} :
  0 ≤ a -> 0 ≤ b -> a < c -> b < d -> a * b < c * d := by
  intro ha hb ac bd
  have cpos := lt_of_le_of_lt ha ac
  have dpos := lt_of_le_of_lt hb bd
  rcases Or.symm (lt_or_eq_of_le ha) with ha | ha
  subst a
  rw [zero_mul]; rw [zero_lt_iff_pos] at *
  exact mul_pos_of_pos_of_pos c d cpos dpos
  rcases Or.symm (lt_or_eq_of_le hb) with hb | hb
  subst b
  rw [mul_zero]; rw [zero_lt_iff_pos] at *
  exact mul_pos_of_pos_of_pos c d cpos dpos
  apply lt_trans
  apply mul_lt_mul_of_pos_left
  assumption
  assumption
  apply mul_lt_mul_of_pos_right
  assumption
  assumption

def mul_le_mul_of_nonneg {a b c d: ℝ} :
  0 ≤ a -> 0 ≤ b -> a ≤ c -> b ≤ d -> a * b ≤ c * d := by
  intro ha hb ac bd
  rcases Or.symm (lt_or_eq_of_le ha) with ha | ha
  subst a
  rw [zero_mul]
  apply mul_nonneg_of_nonneg_of_nonneg
  assumption
  apply le_trans hb
  assumption
  apply le_trans
  apply mul_le_mul_of_nonneg_left
  assumption; assumption
  apply mul_le_mul_of_nonneg_right
  apply flip le_trans <;> assumption
  assumption

def mul_nonneg {a b: ℝ} (ha: 0 ≤ a) (hb: 0 ≤ b) : 0 ≤ a * b := mul_nonneg_of_nonneg_of_nonneg a b ha hb

def mul_pos {a b: ℝ} (ha: 0 < a) (hb: 0 < b) : 0 < a * b := by
  rw [zero_lt_iff_pos] at *
  apply mul_pos_of_pos_of_pos
  assumption
  assumption

def add_nonneg {a b: ℝ} (ha: 0 ≤ a) (hb: 0 ≤ b) : 0 ≤ a + b := by
  rw [←add_zero 0]
  apply le_trans
  apply le_iff_add_le_add_left.mp
  assumption
  apply le_iff_add_le_add_right.mp
  assumption

@[norm_cast]
def ofRat_lt {a b: ℚ} : (a: ℝ) < b ↔ a < b := by
  apply Iff.intro
  · intro h
    obtain ⟨B, B_pos, k, spec⟩ := h
    have : B ≤ b - a := spec k (le_refl _)
    rw [←Rat.add_le_iff_le_sub] at this
    apply lt_of_lt_of_le _ this
    rw (occs := [1]) [←zero_add a]
    apply Rat.add_lt_add_right.mp
    assumption
  · intro h
    exists b - a
    apply And.intro
    rw [←Rat.add_lt_iff_lt_sub, zero_add]; assumption
    exists 0
    intro n _
    apply le_refl

@[norm_cast]
def ofRat_le {a b: ℚ} : (a: ℝ) ≤ b ↔ a ≤ b := by
  apply le_iff_of_lt_iff
  apply ofRat_lt

end Real

namespace CauchySeq

def le_eventually_pointwise (a b: CauchySeq) :
  (Eventually fun n => a n ≤ b n) ->
  Real.mk a ≤ Real.mk b := by
  intro h
  rw [le_iff_not_lt]
  intro ⟨B, B_pos, spec⟩
  replace spec := h.merge spec; clear h
  obtain ⟨k, spec⟩ := spec
  replace spec := spec k (le_refl _)
  obtain ⟨h, spec⟩ := spec
  replace spec: 0 < a _ - b _ := lt_of_lt_of_le B_pos spec
  replace spec := Rat.add_lt_add_of_lt_of_le spec (le_refl (b k))
  rw [zero_add, sub_eq_add_neg, add_assoc, neg_add_cancel,
    add_zero] at spec
  exact not_le_of_lt spec h

def le_pointwise (a b: CauchySeq) :
  (∀n, a n ≤ b n) ->
  Real.mk a ≤ Real.mk b := by
  intro h
  apply le_eventually_pointwise
  exists 0
  intro n g
  apply h

end CauchySeq
