import Math.Data.Rat.Basic
import Math.Order.Linear

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

end Rat
