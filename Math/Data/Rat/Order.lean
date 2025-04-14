import Math.Data.Rat.Basic
import Math.Order.Linear
import Math.Algebra.GroupWithZero.Basic
import Math.Ops.CheckedOrder
import Math.Algebra.Field.Basic
import Math.Algebra.Archimedean.Basic

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
  refine Int.sign_nonneg_iff.mp ?_
  rw [show b.num.sign = a.num.sign from ?_]
  refine Int.sign_nonneg_iff.mpr ?_
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
def isPos.neg {a: ℚ} : ¬a.isNonneg ↔ (-a).isPos := by
  cases a
  simp [Fract.isNonneg, Fract.isPos, ←lt_iff_not_le]
def isPos.mul {a b: ℚ} (ha: a.isPos) : b.isPos ↔ (a * b).isPos := by
  cases a, b with | mk a b =>
  simp [Fract.isPos, ← Int.sign_eq_one_iff_pos] at *
  simp [ha]

def isNonneg.antisymm {a: ℚ} : a.isNonneg -> (-a).isNonneg -> a = 0 := by
  intro ha hb
  cases a with | mk a =>
  simp [Fract.isNonneg] at ha hb
  have := Int.neg_le_neg hb
  have := le_antisymm this ?_
  apply sound
  show _ = _
  simp [this]
  omega
  omega

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

instance : IsDecidableLinearOrder ℚ := {
  inferInstanceAs (IsLinearOrder ℚ),
  instLatticeOfLe ℚ with
}

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
def half_lt (a: ℚ) (h: 0 < a) : a /? 2 < a := by
  conv => { rhs; rw [add_half a] }
  conv => { lhs; rw [←add_zero (_ /? _)] }
  apply add_lt_add_of_le_of_lt
  rfl
  rw [div?_eq_mul_inv?]
  apply mul_pos
  assumption
  decide
def le_add_left_nonneg (a b: ℚ) (h: 0 ≤ b) : a ≤ b + a := by
  conv => { lhs; rw [←zero_add a] }
  apply add_le_add_right.mp
  assumption
def le_add_right_nonneg (a b: ℚ) (h: 0 ≤ b) : a ≤ a + b := by
  conv => { lhs; rw [←add_zero a] }
  apply add_le_add_left.mp
  assumption

instance : IsStrictOrderedSemiring ℚ where
  add_le_add_left := by
    intro a b h c
    apply Rat.add_le_add_left.mp
    assumption
  zero_le_one := by decide
  mul_nonneg := by
    intro a b ha hb
    cases lt_or_eq_of_le ha
    cases lt_or_eq_of_le hb
    apply le_of_lt
    apply Rat.mul_pos
    assumption
    assumption
    subst b
    rw [mul_zero]
    subst a
    rw [zero_mul]
  mul_le_mul_of_nonneg_left := by
    exact fun a b a_1 c a_2 => Rat.mul_le_mul_of_left_nonneg a b c a_2 a_1
  mul_le_mul_of_nonneg_right := by
    exact fun a b a_1 c a_2 => Rat.mul_le_mul_of_right_nonneg a b c a_2 a_1
  mul_pos := by
    exact fun a b a_1 a_2 => Rat.mul_pos a_1 a_2

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

@[norm_cast]
def intCast_le_intCast {a b: ℤ} : (a: ℚ) ≤ b ↔ a ≤ b := by
  rw [le_def]
  show Fract.isNonneg _ ↔ _
  unfold Fract.isNonneg
  simp
  omega

@[norm_cast]
def intCast_lt_intCast {a b: ℤ} : (a: ℚ) < b ↔ a < b := by
  apply lt_iff_of_le_iff
  apply intCast_le_intCast

@[norm_cast]
def natCast_le_natCast {a b: ℕ} : (a: ℚ) ≤ b ↔ a ≤ b := by
  apply (intCast_le_intCast (a := a) (b := b)).trans
  exact Int.ofNat_le

@[norm_cast]
def natCast_lt_natCast {a b: ℕ} : (a: ℚ) < b ↔ a < b := by
  apply lt_iff_of_le_iff
  apply natCast_le_natCast

def midpoint_of_lt {a b: ℚ} (h: a < b) : a < midpoint a b ∧ midpoint a b < b := by
  rw [midpoint]
  rw [lt_div_iff_mul_lt_of_pos, div_lt_iff_lt_mul_of_pos,
    mul_two, mul_two]
  apply And.intro
  exact add_lt_add_left.mp h
  exact add_lt_add_right.mp h
  decide
  decide

def ofInt_le (a b: ℤ) : a ≤ b ↔ a ≤ (b: ℚ) := by
  show _ ↔ (b - (a: ℚ)).isNonneg
  norm_cast
  show _ ↔ 0 ≤ (b - a)
  omega
@[norm_cast]
def intCast_le {a b: Int} : (a: ℚ) ≤ (b: ℚ) ↔ a ≤ b := by
  show (b - (a: ℚ)).isNonneg ↔ _
  norm_cast
  show 0 ≤ (b - a) ↔ _
  omega
@[norm_cast]
def intCast_lt {a b: Int} : (a: ℚ) < (b: ℚ) ↔ a < b := by
  apply lt_iff_of_le_iff
  apply intCast_le

def Fract.floor (a: Fract) := a.num / (a.den: Int)
def Fract.floor.spec (a b: Fract) : a ≈ b -> a.floor = b.floor := by
  intro h
  unfold floor
  suffices ∀a: Fract, a.num / (a.den: ℤ) = a.reduce.num / a.reduce.den by
    rw [this, this b]
    rw [Fract.isReduced.spec a.reduce b.reduce (Fract.reduce.isReduced _) (Fract.reduce.isReduced _)]
    apply (Fract.reduce.spec a).symm.trans
    apply h.trans
    apply Fract.reduce.spec b
  intro a
  let g := ‖a.num‖.gcd a.den
  have g_nz : g ≠ 0 := by
    unfold g
    intro h'
    rw [Nat.gcd_eq_zero_iff] at h'
    exact a.den_nz h'.right
  unfold reduce
  simp
  rw (occs := [1]) [←mul_one a.num, ←mul_one (a.den: ℤ)]
  rw (occs := [1, 2]) [←Int.ediv_self (Int.ofNat_ne_zero.mpr g_nz)]
  rw [←Int.mul_ediv_assoc, ←Int.mul_ediv_assoc]
  rw [mul_comm _ (g: ℤ), mul_comm _ (g: ℤ)]
  rw [Int.mul_ediv_assoc, Int.mul_ediv_assoc _ (b := a.den)]
  show _ = (a.num / g) / (a.den / g)
  apply Int.mul_ediv_mul_of_pos
  refine Int.ofNat_pos.mpr ?_
  exact Nat.zero_lt_of_ne_zero g_nz
  refine Int.ofNat_dvd.mpr ?_
  all_goals unfold g
  apply Nat.gcd_dvd_right
  rw [←Int.natAbs_ofNat a.den]
  show (Int.gcd a.num a.den: ℤ) ∣ _
  exact Int.gcd_dvd_left
  apply Int.dvd_refl
  apply Int.dvd_refl

def floor : ℚ -> Int := by
  apply Quotient.lift Fract.floor
  apply Fract.floor.spec
def ceil (a: ℚ) : Int := -Rat.floor (-a)
def floor_spec (a: ℚ) (x: Int) : a.floor = x ↔ x ≤ a ∧ a < x + 1 := by
  cases a with | mk a =>
  show a.floor = _ ↔ _
  apply Iff.intro
  · rintro rfl
    rw [le_def, lt_def]
    apply And.intro
    · show Fract.isNonneg _
      unfold Fract.floor
      unfold Fract.isNonneg
      rw [Fract.sub_eq_add_neg]
      show 0 ≤ _ + _
      simp [←neg_mul_left]
      apply Int.le_sub_left_of_add_le
      simp; rw [Int.mul_comm]
      apply Int.mul_ediv_self_le
      exact a.den_nz'
    · show 0 < _
      simp [Fract.floor, Int.add_mul]
      rw (occs := [2]) [←Int.ediv_add_emod a.num a.den]
      rw [sub_eq_add_neg, neg_add_rev]
      rw [show a.num / ↑a.den * ↑a.den + ↑a.den + (-(a.num % ↑a.den) + -(↑a.den * (a.num / ↑a.den)))
        = (↑a.den * (a.num / ↑a.den) + -(↑a.den * (a.num / ↑a.den))) + (↑a.den + -(a.num % ↑a.den)) by ac_rfl]
      rw [add_neg_cancel, zero_add]
      apply Int.lt_sub_left_of_add_lt
      rw [add_zero]
      refine Int.emod_lt_of_pos a.num ?_
      exact Int.ofNat_pos.mpr a.den_pos
  · show Fract.isNonneg _ ∧ Fract.isPos _ -> _
    simp [Fract.isNonneg, Fract.isPos, add_mul]
    intro h g
    unfold Fract.floor
    apply Relation.eq_of_not_lt_or_gt (· < ·)
    intro floor_lt
    replace h := Int.add_le_add_right h (x * a.den)
    simp [sub_add_cancel] at h
    have := not_lt_of_le ((Int.le_ediv_iff_mul_le ?_).mpr h)
    contradiction
    apply Int.ofNat_pos.mpr a.den_pos
    intro lt_floor
    rw (occs := [2]) [←one_mul (a.den: ℤ)] at g
    rw [←add_mul] at g
    replace g := Int.add_lt_add_right g a.num
    rw [zero_add, sub_add_cancel] at g
    replace g := Int.ediv_lt_of_lt_mul (Int.ofNat_pos.mpr a.den_pos) g
    have := not_lt_of_le (Int.le_iff_lt_add_one.mpr g)
    contradiction
def ceil_spec (a: ℚ) (x: Int) : a.ceil = x ↔ x - 1 < a ∧ a ≤ x := by
  unfold ceil
  rw (occs := [1]) [←neg_neg x]
  rw [neg_inj, floor_spec, ←intCast_neg, ←neg_le_neg_iff]
  norm_cast
  rw [←neg_neg ((-x + 1: ℤ): ℚ), intCast_neg,
    neg_add_rev, neg_neg, add_comm _ x, ←sub_eq_add_neg,
    ←neg_lt_neg_iff]
  apply And.comm
def ceil_eq_neg_floor_neg (a: ℚ) : a.ceil = -(-a).floor := rfl
def floor_eq_neg_ceil_neg (a: ℚ) : a.floor = -(-a).ceil := by
  rw [ceil_eq_neg_floor_neg, neg_neg, neg_neg]

attribute [irreducible] floor ceil

def floor_le_self (a: ℚ) : a.floor ≤ a := ((floor_spec a a.floor).mp rfl).left
def self_le_ceil (a: ℚ) : a ≤ a.ceil := ((ceil_spec a a.ceil).mp rfl).right
def floor_le (a: ℚ) : ∀x: ℤ, a ≤ x -> a.floor ≤ x := by
  intro x hx
  have := le_trans ((floor_spec a a.floor).mp rfl).left hx
  rw [←ofInt_le] at this
  assumption
def le_ceil (a: ℚ) : ∀x: ℤ, x ≤ a -> x ≤ a.ceil := by
  intro x hx
  have := le_trans hx ((ceil_spec a a.ceil).mp rfl).right
  rw [←ofInt_le] at this
  assumption
def of_floor_lt (a: ℚ) : ∀x: ℤ, a.floor < x -> a < x := by
  intro x hx
  have := ((floor_spec a a.floor).mp rfl).right
  rw [←intCast_one, intCast_add] at this
  apply lt_of_lt_of_le this
  rw [intCast_le, Int.add_one_le_iff]
  assumption
def of_lt_ceil (a: ℚ) : ∀x: ℤ, x < a.ceil -> x < a := by
  intro x hx
  rw [ceil_eq_neg_floor_neg,
    ←neg_neg x, Int.neg_lt_neg_iff] at hx
  have := of_floor_lt _ _ hx
  rw [←intCast_neg, ←neg_lt_neg_iff] at this
  assumption
def of_le_floor (a: ℚ) : ∀x: ℤ, x ≤ a.floor -> x ≤ a := by
  intro x h
  rw [←intCast_le] at h
  apply le_trans h
  apply floor_le_self
def of_ceil_le (a: ℚ) : ∀x: ℤ, a.ceil ≤ x -> a ≤ x := by
  intro x h
  rw [←intCast_le] at h
  apply le_trans _ h
  apply self_le_ceil
def of_lt_floor (a: ℚ) : ∀x: ℤ, x < a.floor -> x < a := by
  intro x h
  rw [←intCast_lt] at h
  apply lt_of_lt_of_le h
  apply floor_le_self
def of_ceil_lt (a: ℚ) : ∀x: ℤ, a.ceil < x -> a < x := by
  intro x h
  rw [←intCast_lt] at h
  apply lt_of_le_of_lt _ h
  apply self_le_ceil
def ceil_lt (a: ℚ) : ∀x: ℤ, x ≤ a -> x ≤ a.ceil := by
  intro x hx
  have := le_trans hx ((ceil_spec a a.ceil).mp rfl).right
  rw [←ofInt_le] at this
  assumption
def fract (a: ℚ) : ℚ := a - a.floor
def floor_add_fract (a: ℚ) : a.floor + a.fract = a := add_sub_cancel _ _
def sub_fract (a: ℚ) : a - a.fract = a.floor := by
  unfold fract
  rw [sub_sub, add_sub_assoc, add_sub_cancel]
def fract_spec (a: ℚ) : 0 ≤ a.fract ∧ a.fract < 1 := by
  unfold fract
  rw [←add_le_iff_le_sub, zero_add, ←lt_add_iff_sub_lt, add_comm]
  apply (floor_spec _ _).mp
  rfl

def le_floor_of_lt_ceil (a: ℚ) : ∀x: ℤ, x < a.ceil -> x ≤ a.floor := by
  intro x h
  have := of_lt_ceil _ _ h
  have :=  lt_trans this ((floor_spec a a.floor).mp rfl).right
  rw [←intCast_succ, intCast_lt] at this
  apply Int.le_of_lt_add_one
  assumption

@[simp]
def intCast_floor (a: ℤ) : floor a = a := by
  apply (floor_spec _ _).mpr
  rw [←intCast_succ, intCast_le, intCast_lt]
  omega

@[simp]
def intCast_ceil (a: ℤ) : ceil a = a := by
  apply (ceil_spec _ _).mpr
  rw [←intCast_pred, intCast_le, intCast_lt]
  omega

def le_floor (a: ℚ) : ∀x: ℤ, x ≤ a.floor ↔ x ≤ a := by
  intro x
  apply Iff.intro
  apply of_le_floor
  intro h
  rcases lt_or_eq_of_le (le_ceil _ _ h) with h | h
  apply le_floor_of_lt_ceil; assumption
  subst x
  have := le_antisymm h (self_le_ceil _)
  rw [←this]
  simp
def ceil_le (a: ℚ) : ∀x: ℤ, a.ceil ≤ x ↔ a ≤ x := by
  intro x
  rw [ceil_eq_neg_floor_neg, ←Int.neg_le_neg_iff, neg_neg]
  rw [le_floor, ←intCast_neg, ←neg_le_neg_iff]

end Rat

instance : Archimedean ℚ := by
  apply archimedean_iff_nat_lt.mpr
  intro x
  exists (x.ceil + 1).natAbs
  apply flip lt_of_lt_of_le
  show ((x.ceil + 1: ℤ): ℚ) ≤ _
  rw [←intCast_ofNat, Rat.intCast_le]
  apply Int.le_natAbs
  apply lt_of_le_of_lt
  apply Rat.self_le_ceil
  rw [Rat.intCast_lt]
  exact Int.lt_succ x.ceil

section

open Norm.ofAbs

instance : Norm ℚ ℚ := inferInstance
instance : IsModuleNorm ℚ ℚ := inferInstance
instance : IsAlgebraNorm ℚ := inferInstance

end
