import Math.Data.Rat.Basic
import Math.Order.Linear
import Math.Algebra.GroupWithZero.Basic
import Math.Ops.CheckedOrder

namespace Rat

def Fract.isNonneg (f: Fract) : Prop := 0 ≤ f.num
def Fract.isPos (f: Fract) : Prop := 0 < f.num

def isNonneg : ℚ -> Prop := by
  apply Quotient.lift Fract.isNonneg
  suffices ∀a b: Fract, a ≈ b -> a.isNonneg -> b.isNonneg by
    intro a b eq
    apply propext
    apply Iff.intro
    apply this <;> assumption
    apply this <;> (apply Relation.symm; assumption)
  intro a b eq ha
  replace eq : _ = _ := eq
  unfold Fract.isNonneg at *
  refine Int.sign_nonneg.mp ?_
  rw [show b.num.sign = a.num.sign from ?_]
  refine Int.sign_nonneg.mpr ?_
  assumption
  have : (b.num * a.den).sign = (a.num * b.den).sign := by rw [eq]
  rw [Int.sign_mul, Int.sign_mul, Int.sign_ofNat_of_nonzero a.den_nz,
    Int.sign_ofNat_of_nonzero b.den_nz, Int.mul_one, Int.mul_one] at this
  assumption

def isPos : ℚ -> Prop := by
  apply Quotient.lift Fract.isPos
  suffices ∀a b: Fract, a ≈ b -> a.isPos -> b.isPos by
    intro a b eq
    apply propext
    apply Iff.intro
    apply this <;> assumption
    apply this <;> (apply Relation.symm; assumption)
  intro a b eq ha
  replace eq : _ = _ := eq
  unfold Fract.isNonneg at *
  refine Int.sign_eq_one_iff_pos.mp ?_
  rw [show b.num.sign = a.num.sign from ?_]
  refine Int.sign_eq_one_iff_pos.mpr ?_
  assumption
  have : (b.num * a.den).sign = (a.num * b.den).sign := by rw [eq]
  rw [Int.sign_mul, Int.sign_mul, Int.sign_ofNat_of_nonzero a.den_nz,
    Int.sign_ofNat_of_nonzero b.den_nz, Int.mul_one, Int.mul_one] at this
  assumption

@[simp]
def mk_isNonneg (a: Fract) : ⟦a⟧.isNonneg = a.isNonneg := rfl
@[simp]
def mk_isPos (a: Fract) : ⟦a⟧.isPos = a.isPos := rfl

def isNonneg.add {a b: ℚ} (ha: a.isNonneg) (hb: b.isNonneg) : (a + b).isNonneg := by
  cases a, b with | mk a b =>
  simp [Fract.isNonneg] at *
  refine Int.add_nonneg ?_ ?_ <;> refine Int.mul_nonneg ?_ ?_
  assumption
  exact Int.ofNat_zero_le b.den
  assumption
  exact Int.ofNat_zero_le a.den
def isNonneg.mul {a b: ℚ} (ha: a.isNonneg) (hb: b.isNonneg) : (a * b).isNonneg := by
  cases a, b with | mk a b =>
  simp [Fract.isNonneg] at *
  refine Int.mul_nonneg ?_ ?_
  assumption
  assumption
def isNonneg.neg {a: ℚ} : ¬a.isPos ↔ (-a).isNonneg := by
  cases a
  simp [Fract.isNonneg, Fract.isPos, ←lt_iff_not_le]
  omega
def isPos.neg {a: ℚ} : ¬a.isNonneg ↔ (-a).isPos := by
  cases a
  simp [Fract.isNonneg, Fract.isPos, ←lt_iff_not_le]
  omega
def isPos.mul {a b: ℚ} (ha: a.isPos) : b.isPos ↔ (a * b).isPos := by
  cases a, b with | mk a b =>
  simp [Fract.isPos, ← Int.sign_eq_one_iff_pos] at *
  simp [ha]

def isNonneg.antisymm {a: ℚ} : a.isNonneg -> (-a).isNonneg -> a = 0 := by
  intro ha hb
  cases a with | mk a =>
  simp [Fract.isNonneg] at ha hb
  have := Int.neg_le_neg hb
  rw [Int.neg_neg] at this
  have := le_antisymm this ha
  apply sound
  show _ = _
  simp [this]

instance : LE ℚ where
  le a b := (b - a).isNonneg
instance : LT ℚ where
  lt a b := (b - a).isPos

def le_def (a b: ℚ) : (a ≤ b) = (b - a).isNonneg := rfl
def lt_def (a b: ℚ) : (a < b) = (b - a).isPos := rfl

instance : IsLinearOrder ℚ where
  lt_iff_le_and_not_le := by
    intro a b
    cases a, b with | mk a b =>
    simp [lt_def ,le_def, Fract.isPos, Fract.isNonneg]
    omega
  lt_or_le a b := by
    cases a, b with | mk a b =>
    simp [lt_def, le_def]
    rcases lt_or_le 0 (b - a).num
    left; assumption
    right; rename_i h
    have := (isNonneg.neg (a := ⟦b - a⟧)).mp (not_lt_of_le h)
    rw [←mk_sub, neg_sub] at this
    assumption
  le_trans := by
    intro a b c ab bc
    cases a, b, c with | mk a b c =>
    simp only [le_def] at *
    rw [←add_zero (_ - _), ←sub_self ⟦b⟧, sub_add_assoc, ←add_sub_assoc, add_comm (-⟦a⟧),
      sub_eq_add_neg, add_comm _ (-⟦b⟧), ←add_assoc, ←sub_eq_add_neg, ←sub_eq_add_neg]
    apply isNonneg.add
    assumption
    assumption
  le_antisymm := by
    intro a b ha hb
    simp [le_def] at ha hb
    rw [←neg_sub] at ha
    have := isNonneg.antisymm hb ha
    apply eq_of_sub_eq_zero
    assumption

instance (q: ℚ) : Decidable q.isNonneg := by
  apply q.recOnSubsingleton (motive := fun _ => _)
  intro q
  exact inferInstanceAs (Decidable (0 ≤ q.num))
instance (q: ℚ) : Decidable q.isPos :=
  decidable_of_iff (¬(-q).isNonneg) (by rw [isPos.neg, neg_neg])

instance : DecidableLE ℚ := inferInstanceAs (∀a b: ℚ, Decidable (b - a).isNonneg)
instance : DecidableLT ℚ := inferInstanceAs (∀a b: ℚ, Decidable (b - a).isPos)

instance : Min ℚ := minOfLe
instance : Max ℚ := maxOfLe

instance : IsDecidableLinearOrder ℚ where

def Fract.abs (f: Fract) : Fract where
  num := ‖f.num‖
  den := f.den
  den_pos := f.den_pos

instance : AbsoluteValue Fract Fract := ⟨.abs⟩

@[simp]
def Fract.abs_num (a: Fract) : ‖a‖.num = ‖a.num‖ := rfl
@[simp]
def Fract.abs_den (a: Fract) : ‖a‖.den = a.den := rfl

def Fract.abs.spec (a b: Fract) : a ≈ b -> ‖a‖ ≈ ‖b‖ := by
  intro eqv
  show _ * _ = _ * _
  have : ‖a‖.num = ‖a.num‖ := rfl
  rw [this]
  have : ‖b‖.num = ‖b.num‖ := rfl
  rw [this]
  have : ‖a‖.den = ‖Int.ofNat a.den‖ := rfl
  rw [this]
  have : ‖b‖.den = ‖Int.ofNat b.den‖ := rfl
  rw [this]
  rw [Int.ofNat_mul_ofNat, Int.ofNat_mul_ofNat]
  congr 1
  show Int.natAbs a.num * Int.natAbs b.den = Int.natAbs b.num * Int.natAbs a.den
  rw [←Int.natAbs_mul, eqv, ←Int.natAbs_mul]

instance : AbsoluteValue ℚ ℚ where
  abs := by
    apply Quotient.lift (⟦‖·‖⟧)
    intro a b eq
    apply sound
    apply Fract.abs.spec
    assumption

@[simp]
def mk_abs (a: Fract) : ‖⟦a⟧‖ = ⟦‖a‖⟧ := rfl

def abs_def (q: ℚ) : ‖q‖ = if 0 ≤ q then q else -q := by
  cases q with | mk q =>
  simp
  split <;> (apply sound; show _ = _)
  congr 1
  rename_i h
  rw [le_def, sub_zero] at h
  exact Int.natAbs_of_nonneg h
  congr 1
  rename_i h
  rw [le_def, sub_zero] at h
  show q.num.natAbs = (-q.num)
  rw [←Int.natAbs_neg]
  apply Int.natAbs_of_nonneg
  replace h: (-q).isPos := isPos.neg.mp h
  apply le_of_lt h

def abs_nonzero (a: ℚ) : a ≠ 0 -> ‖a‖ ≠ 0 := by
  cases a with | mk a =>
  intro ha
  simp
  replace ha := exact_ne ha
  intro h
  apply ha
  clear ha
  replace h: a.abs ≈ 0 := exact h
  unfold Fract.abs at h
  simp [AbsoluteValue.abs] at h
  replace h : _ = _ := h
  simp at h
  erw [Int.mul_one, Int.zero_mul] at h
  show _ = _
  erw [Int.mul_one, Int.zero_mul]
  refine Int.natAbs_eq_zero.mp ?_
  apply Int.ofNat.inj
  assumption

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply abs_nonzero <;> assumption)

def neg_le_neg_iff {a b: ℚ} : a ≤ b ↔ -b ≤ -a := by
  rw [le_def, le_def, neg_sub_neg]
def neg_lt_neg_iff {a b: ℚ} : a < b ↔ -b < -a := by
  rw [lt_def, lt_def, neg_sub_neg]

-- def nonneg_iff_sign_nonneg {a: ℚ} : 0 ≤ a ↔ 0 ≤ a.sign := by sorry
-- def Fract.nonneg_iff_sign_nonneg {a: Fract} : 0 ≤ a ↔ 0 ≤ a.sign := by sorry
-- def nonpos_iff_sign_nonpos {a: ℚ} : a ≤ 0 ↔ a.sign ≤ 0 := by sorry
-- def pos_iff_sign_pos {a: ℚ} : 0 < a ↔ 0 < a.sign := by sorry
-- def Fract.pos_iff_sign_pos {a: Fract} : 0 < a ↔ 0 < a.sign := by sorry
-- def neg_iff_sign_neg {a: ℚ} : a < 0 ↔ a.sign < 0 := by sorry
-- def eq_zero_iff_sign_eq_zero {a: ℚ} : a = 0 ↔ a.sign = 0 := by sorry

def abs_nonneg (a: ℚ) : 0 ≤ ‖a‖ := by
  rw [abs_def]
  split
  assumption
  rename_i h
  rw [le_def, sub_zero]; rw [le_def, sub_zero] at h
  apply isNonneg.neg.mp
  intro g; apply h
  cases a
  exact le_of_lt (α := Int) g
def abs_pos (a: ℚ) : a ≠ 0 -> 0 < ‖a‖ := by
  intro h
  apply lt_of_le_of_ne
  apply abs_nonneg
  intro g
  have := (abs_nonzero _ h).symm
  contradiction
def add_le_add_right {a b k: ℚ} : a ≤ b ↔ a + k ≤ b + k := by
  rw [le_def, le_def, add_sub_assoc, sub_add, sub_self, zero_sub, sub_eq_add_neg]
def add_le_add_left {a b k: ℚ} : a ≤ b ↔ k + a ≤ k + b := by
  rw [add_comm k, add_comm k]
  apply add_le_add_right
def add_lt_add_right {a b k: ℚ} : a < b ↔ a + k < b + k := by
  apply lt_iff_of_le_iff
  apply add_le_add_right
def add_lt_add_left {a b k: ℚ} : a < b ↔ k + a < k + b := by
  apply lt_iff_of_le_iff
  apply add_le_add_left
def add_le_add {a b c d: ℚ} : a ≤ c -> b ≤ d -> a + b ≤ c + d := by
  intro ac bd
  apply le_trans
  apply add_le_add_right.mp
  assumption
  apply add_le_add_left.mp
  assumption
def add_lt_add {a b c d: ℚ} : a < c -> b < d -> a + b < c + d := by
  intro ac bd
  apply lt_trans
  apply add_lt_add_right.mp
  assumption
  apply add_lt_add_left.mp
  assumption
def add_lt_add_of_lt_of_le {a b c d: ℚ} : a < c -> b ≤ d -> a + b < c + d := by
  intro ac bd
  apply lt_of_lt_of_le
  apply add_lt_add_right.mp
  assumption
  apply add_le_add_left.mp
  assumption
def add_lt_add_of_le_of_lt {a b c d: ℚ} : a ≤ c -> b < d -> a + b < c + d := by
  intro ac bd
  apply lt_of_le_of_lt
  apply add_le_add_right.mp
  assumption
  apply add_lt_add_left.mp
  assumption
def add_neg_lt_left (a b: ℚ) : b < 0 -> a + b < a := by
  intro h
  conv => { rhs; rw [←add_zero a] }
  apply add_lt_add_of_le_of_lt
  rfl
  assumption
def left_le_add_nonneg (a b: ℚ) : 0 ≤ b -> a ≤ a + b := by
  intro h
  conv => { lhs; rw [←add_zero a] }
  apply add_le_add
  rfl
  assumption
def add_nonneg (a b: ℚ) : 0 ≤ a -> 0 ≤ b -> 0 ≤ a + b := by
  intro ha hb
  rw [←add_zero 0]
  apply add_le_add <;> assumption
def add_nonpos (a b: ℚ) : a ≤ 0 -> b ≤ 0 -> a + b ≤ 0 := by
  intro ha hb
  rw [←add_zero 0]
  apply add_le_add <;> assumption

def add_le_iff_le_sub {a b k: ℚ} : a + k ≤ b ↔ a ≤ b - k := by
  rw [add_le_add_right (k := -k), add_assoc, add_neg_cancel, add_zero, sub_eq_add_neg]
def le_add_iff_sub_le {a b k: ℚ} : a ≤ b + k ↔ a - k ≤ b := by
  rw [add_le_add_right (k := -k), add_assoc, add_neg_cancel, add_zero, sub_eq_add_neg]

def add_lt_iff_lt_sub {a b k: ℚ} : a + k < b ↔ a < b - k := by
  apply lt_iff_of_le_iff
  apply le_add_iff_sub_le
def lt_add_iff_sub_lt {a b k: ℚ} : a < b + k ↔ a - k < b := by
  apply lt_iff_of_le_iff
  apply add_le_iff_le_sub

def lt_iff_mul_left_pos {a b k: ℚ} : 0 < k -> (a < b ↔ k * a < k * b) := by
  intro kpos
  rw [lt_def, lt_def, ←mul_sub]
  apply isPos.mul
  rw [lt_def, sub_zero] at kpos
  assumption
def lt_iff_mul_right_pos {a b k: ℚ} : 0 < k -> (a < b ↔ a * k < b * k) := by
  rw [mul_comm _ k, mul_comm _ k]
  apply lt_iff_mul_left_pos
def le_iff_mul_left_pos {a b k: ℚ} : 0 < k -> (a ≤ b ↔ k * a ≤ k * b) := by
  intro kpos
  apply le_iff_of_lt_iff
  apply lt_iff_mul_left_pos
  assumption
def le_iff_mul_right_pos {a b k: ℚ} : 0 < k -> (a ≤ b ↔ a * k ≤ b * k) := by
  intro kpos
  apply le_iff_of_lt_iff
  apply lt_iff_mul_right_pos
  assumption
def mul_lt_mul {a b c d: ℚ} : 0 < a -> a < c -> 0 < b -> b < d -> a * b < c * d := by
  intro apos ac bpos bd
  apply lt_trans
  apply (lt_iff_mul_left_pos _).mp
  assumption
  assumption
  apply (lt_iff_mul_right_pos _).mp
  assumption
  apply lt_trans <;> assumption
def mul_le_mul_of_right_nonneg (a b k: ℚ) : 0 ≤ k -> a ≤ b -> a * k ≤ b * k := by
  intro knonneg a_le_b
  rcases lt_or_eq_of_le knonneg with h | h
  apply (le_iff_mul_right_pos h).mp
  assumption
  rw [←h, mul_zero, mul_zero]
def mul_le_mul_of_left_nonneg (a b k: ℚ) : 0 ≤ k -> a ≤ b -> k * a ≤ k * b := by
  intro knonneg a_le_b
  rcases lt_or_eq_of_le knonneg with h | h
  apply (le_iff_mul_left_pos h).mp
  assumption
  rw [←h, zero_mul, zero_mul]
def mul_le_mul_nonneg (a b c d: ℚ) : 0 ≤ a -> a ≤ c -> 0 ≤ b -> b ≤ d -> a * b ≤ c * d := by
  intro ann ac bnn bd
  apply le_trans
  apply mul_le_mul_of_left_nonneg
  assumption
  assumption
  apply mul_le_mul_of_right_nonneg
  apply le_trans <;> assumption
  assumption
def inv_pos (a: ℚ) (h: a ≠ 0 := by invert_tactic) : 0 < a ↔ 0 < a⁻¹? := by
  suffices ∀(a: ℚ) (h: a ≠ 0), 0 < a -> 0 < a⁻¹? by
    apply Iff.intro
    apply this
    intro g
    have := this _ (by invert_tactic) g
    rw [inv?_inv?] at this
    assumption
  clear h a
  intro a h ha
  apply (lt_trichotomy 0 a⁻¹?).resolve_right
  intro g
  rcases g with g | g
  have := g.symm
  have : a⁻¹? ≠ 0 := by invert_tactic
  contradiction
  have := (lt_iff_mul_left_pos ha).mp g
  rw [mul_inv?_cancel, mul_zero] at this
  contradiction

def nonpos_of_le_neg (a: ℚ) : a ≤ -a -> a ≤ 0 := by
  intro h
  rw [le_def, ←neg_sub, sub_eq_add_neg, neg_neg, ←sub_zero (- _), ←le_def, neg_add_rev] at h
  rw [←mul_two] at h
  have := (le_iff_mul_right_pos (k := 2⁻¹?) (by decide)).mp h
  rw [zero_mul, mul_assoc, mul_inv?_cancel, mul_one, neg_le_neg_iff, neg_neg] at this
  assumption
def nonneg_of_neg_le (a: ℚ) : -a ≤ a -> 0 ≤ a := by
  intro h
  rw [neg_le_neg_iff]
  apply nonpos_of_le_neg
  rw [neg_neg]
  assumption
def le_neg_of_nonpos (a: ℚ) : a ≤ 0 -> a ≤ -a := by
  intro h
  apply le_trans h
  rw [neg_le_neg_iff, neg_neg]
  assumption
def neg_le_of_nonneg (a: ℚ) : 0 ≤ a -> -a ≤ a := by
  intro h
  apply le_trans _ h
  rw [neg_le_neg_iff, neg_neg]
  assumption
def abs_add_le_add_abs.helper (a b: ℚ) : a < 0 -> 0 ≤ b -> ‖a + b‖ ≤ -a + b := by
  intro ha hb
  rw [abs_def]
  split
  apply add_le_add_right.mp
  apply add_le_add_left.mpr
  rw [neg_add_cancel]
  rw [neg_le_neg_iff, neg_add_rev, neg_neg]
  apply add_nonpos <;> (apply le_of_lt; assumption)
  rw [neg_add_rev, add_comm]
  apply add_le_add_left.mp
  apply add_le_add_right.mpr
  rw [neg_add_cancel]
  apply add_nonneg <;> assumption
def abs_add_le_add_abs (a b: ℚ) : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := by
  rw [abs_def a, abs_def b]
  split <;> split
  · rw [abs_def, if_pos]
    apply add_nonneg <;> assumption
  · rw [add_comm a, add_comm a]
    apply abs_add_le_add_abs.helper
    rw [not_le] at *; assumption
    assumption
  · apply abs_add_le_add_abs.helper
    rw [not_le] at *; assumption
    assumption
  · rename_i h g
    rw [not_le] at h g
    rw [abs_def, if_neg, neg_add_rev, add_comm]
    rw [not_le]
    rw [←add_zero 0]
    apply add_lt_add <;> assumption

def sub_abs_self_sub (a b: ℚ) : a - ‖a - b‖ ≤ b := by
  rw [abs_def]; split
  rw [sub_sub, add_sub_assoc, add_sub_cancel]
  rw [sub_eq_add_neg, neg_neg]
  rename_i h; rw [not_le] at h
  conv => { rhs; rw [←add_zero b] }
  apply add_le_add
  rw [←lt_add_iff_sub_lt, zero_add] at h
  apply le_of_lt; assumption
  apply le_of_lt; assumption
def sub_le_sub (a b c d: ℚ) : a ≤ c -> d ≤ b -> a - b ≤ c - d := by
  rw [neg_le_neg_iff (a := d) (b := b), sub_eq_add_neg, sub_eq_add_neg]
  apply add_le_add
def mul_pos {a b: ℚ} : 0 < a -> 0 < b -> 0 < a * b := by
  intro ha hb
  have := (lt_iff_mul_right_pos hb).mp ha
  rw [zero_mul] at this
  assumption
def mul_nonneg {a b: ℚ} : 0 ≤ a -> 0 ≤ b -> 0 ≤ a * b := by
  intro ha hb
  rcases lt_or_eq_of_le ha with ha | ha
  rcases lt_or_eq_of_le hb with hb | hb
  apply le_of_lt; apply mul_pos <;> assumption
  rw [←hb, mul_zero]
  rw [←ha, zero_mul]
def pos_mul_lt_of_right_lt_one (a b: ℚ) : 0 < a -> b < 1 -> a * b < a := by
  intro ha hb
  conv => {
    rhs; rw [←mul_one a]
  }
  apply (lt_iff_mul_left_pos _).mp
  assumption
  assumption
def abs_of_nonneg (a: ℚ) : 0 ≤ a -> ‖a‖ = a := by
  intro h
  rw [abs_def, if_pos h]
def abs_of_pos (a: ℚ) : 0 < a -> ‖a‖ = a := by
  intro h
  rw [abs_def, if_pos (le_of_lt h)]
def half_lt (a: ℚ) (h: 0 < a) : a /? 2 < a := by
  conv => { rhs; rw [add_half a] }
  conv => { lhs; rw [←add_zero (_ /? _)] }
  apply add_lt_add_of_le_of_lt
  rfl
  rw [div?_eq_mul_inv?]
  apply mul_pos
  assumption
  decide
def abs_abs (a: ℚ) : ‖‖a‖‖ = ‖a‖ := by
  rw [abs_of_nonneg]
  apply abs_nonneg
def abs_mul (a b: ℚ) : ‖a * b‖ = ‖a‖ * ‖b‖ := by
  simp [abs_def]
  rcases lt_trichotomy 0 a with ha | ha | ha
  <;> rcases lt_trichotomy 0 b with hb | hb | hb
  any_goals rw [if_pos (le_of_lt ha)]
  any_goals rw [if_pos (le_of_lt hb)]
  any_goals rw [←ha]
  any_goals rw [←hb]
  repeat any_goals rw [zero_mul]
  repeat any_goals rw [mul_zero]
  all_goals repeat rw [if_pos (le_refl _)]
  repeat any_goals rw [zero_mul]
  repeat any_goals rw [mul_zero]
  rw [if_pos]
  apply le_of_lt; apply mul_pos <;> assumption
  rw [if_neg (not_le_of_lt hb), if_neg, neg_mul_right]
  rw [not_le, neg_lt_neg_iff, neg_mul_right]
  apply mul_pos; assumption
  rw [neg_lt_neg_iff, neg_neg]; assumption
  rw [if_neg, if_neg, neg_mul_left]
  rw [not_le]; assumption
  rw [not_le, ←neg_neg (_ * _), neg_mul_left, neg_lt_neg_iff, neg_neg];
  apply mul_pos
  rw [neg_lt_neg_iff, neg_neg]; assumption
  assumption
  rw [if_pos, if_neg, if_neg, ←neg_mul_left, ←neg_mul_right, neg_neg]
  any_goals
    rw [not_le]
    assumption
  rw [←neg_neg (_ * _), neg_mul_right, neg_mul_left]
  apply mul_nonneg <;> rw [neg_le_neg_iff, neg_neg]
  repeat apply le_of_lt; assumption
def abs_inv? (a: ℚ) (h: a ≠ 0) : ‖a⁻¹?‖ = ‖a‖⁻¹? := by
  refine inv?_eq_of_mul_right ‖a‖ ‖a⁻¹?‖ ?_
  rw [←abs_mul, inv?_mul_cancel]
  rfl
def abs_div? (a b: ℚ) (h: b ≠ 0) : ‖a /? b‖ = ‖a‖ /? ‖b‖ := by
  rw [div?_eq_mul_inv?, div?_eq_mul_inv?, abs_mul, abs_inv?]
def abs_div_lt_one (a b: ℚ) (h: b ≠ 0) : ‖a /? b‖ < 1 ↔ ‖a‖ < ‖b‖ := by
  rw [lt_iff_mul_right_pos (k := ‖b‖), one_mul, ←abs_mul, div?_eq_mul_inv?,
    mul_assoc, inv?_mul_cancel, mul_one]
  exact abs_pos b h
def le_add_left_nonneg (a b: ℚ) (h: 0 ≤ b) : a ≤ b + a := by
  conv => { lhs; rw [←zero_add a] }
  apply add_le_add_right.mp
  assumption
def le_add_right_nonneg (a b: ℚ) (h: 0 ≤ b) : a ≤ a + b := by
  conv => { lhs; rw [←add_zero a] }
  apply add_le_add_left.mp
  assumption

def le_div_iff_mul_le_of_pos (a b c: ℚ) (h: 0 < b) : c ≤ a /? b ↔ c * b ≤ a := by
  rw [le_iff_mul_right_pos  (k := b), div?_mul_cancel]
  assumption
def le_div_iff_mul_le_of_neg (a b c: ℚ) (h: b < 0) : c ≤ a /? b ↔ a ≤ c * b := by
  rw [le_iff_mul_right_pos  (k := -b), ←neg_mul_right, ←neg_mul_right, div?_mul_cancel,
    ←neg_le_neg_iff]
  rw [neg_lt_neg_iff, neg_neg]
  assumption

def div_le_iff_le_mul_of_pos (a b c: ℚ) (h: 0 < b) : a /? b ≤ c ↔ a ≤ c * b := by
  rw [le_iff_mul_right_pos  (k := b), div?_mul_cancel]
  assumption
def div_le_iff_le_mul_of_neg (a b c: ℚ) (h: b < 0) : a /? b ≤ c ↔ c * b ≤ a := by
  rw [le_iff_mul_right_pos  (k := -b), ←neg_mul_right, div?_mul_cancel,
    ←neg_mul_right, ←neg_le_neg_iff]
  rw [neg_lt_neg_iff, neg_neg]
  assumption

def lt_div_iff_mul_lt_of_pos (a b c: ℚ) (h: 0 < b) : c < a /? b ↔ c * b < a := by
  apply lt_iff_of_le_iff
  apply div_le_iff_le_mul_of_pos
  assumption
def lt_div_iff_mul_lt_of_neg (a b c: ℚ) (h: b < 0) : c < a /? b ↔ a < c * b := by
  apply lt_iff_of_le_iff
  apply div_le_iff_le_mul_of_neg
  assumption

def div_lt_iff_lt_mul_of_pos (a b c: ℚ) (h: 0 < b) : a /? b < c ↔ a < c * b := by
  apply lt_iff_of_le_iff
  apply le_div_iff_mul_le_of_pos
  assumption
def div_lt_iff_lt_mul_of_neg (a b c: ℚ) (h: b < 0) : a /? b < c ↔ c * b < a := by
  apply lt_iff_of_le_iff
  apply le_div_iff_mul_le_of_neg
  assumption

def intCast_le_intCast {a b: ℤ} : (a: ℚ) ≤ b ↔ a ≤ b := by
  rw [le_def]
  show Fract.isNonneg _ ↔ _
  unfold Fract.isNonneg
  simp
  omega

def intCast_lt_intCast {a b: ℤ} : (a: ℚ) < b ↔ a < b := by
  apply lt_iff_of_le_iff
  apply intCast_le_intCast

def natCast_le_natCast {a b: ℕ} : (a: ℚ) ≤ b ↔ a ≤ b := by
  apply (intCast_le_intCast (a := a) (b := b)).trans
  exact Int.ofNat_le

def natCast_lt_natCast {a b: ℕ} : (a: ℚ) < b ↔ a < b := by
  apply lt_iff_of_le_iff
  apply natCast_le_natCast

def eq_zero_iff_abs_eq_zero {a: ℚ} : a = 0 ↔ ‖a‖ = 0 := by
  rw [abs_def]
  split <;> apply Iff.intro <;> intro h
  any_goals assumption
  apply neg_inj.mp; rw [neg_neg]
  assumption
  apply neg_inj.mp
  assumption

-- def floor (a: ℚ) : Int := a.num.ediv (a.den: Int)
-- def ceil (a: ℚ) : Int := -Rat.floor (-a)
-- private def Fract.sub_one_num (a: Fract) : (a - 1).num = a.num - a.den := by sorry
-- private def Fract.sub_one_den (a: Fract) : (a - 1).den = a.den := Nat.mul_one _
-- private def int_div_one (a: Int) : a / (1: Nat) = a := by sorry
-- private def sub_one_num (a: ℚ) : (a - 1).num = a.num - a.den := by sorry
-- private def sub_one_den (a: ℚ) : (a - 1).den = a.den := by sorry
-- private def add_one_num (a: ℚ) : (a + 1).num = a.num + a.den := by sorry
-- private def add_one_den (a: ℚ) : (a + 1).den = a.den := by sorry
-- def floor_spec (a: ℚ) (x: Int) : a.floor = x ↔ x ≤ a ∧ a < x + 1 := by sorry
-- def ceil_spec (a: ℚ) (x: Int) : a.ceil = x ↔ x - 1 < a ∧ a ≤ x := by sorry
-- def intCast_lt (a b: Int) : (a: ℚ) < (b: ℚ) ↔ a < b := by sorry
-- def intCast_le (a b: Int) : (a: ℚ) ≤ (b: ℚ) ↔ a ≤ b := by sorry
-- def fract (a: ℚ) : ℚ := a - a.floor
-- def floor_add_fract (a: ℚ) : a.floor + a.fract = a := by sorry
-- def sub_fract (a: ℚ) : a - a.fract = a.floor := by sorry
-- def fract_spec (a: ℚ) : 0 ≤ a.fract ∧ a.fract < 1 := by sorry
-- def zero_le_floor (a: ℚ) : 0 ≤ a.floor ↔ 0 ≤ a := by sorry
-- def ceil_le_zero (a: ℚ) : a.ceil ≤ 0 ↔ a ≤ 0 := by sorry

end Rat
