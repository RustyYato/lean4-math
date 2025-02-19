import Math.Algebra.GroupWithZero.Defs
import Math.Algebra.Group.Units.Defs

variable [GroupWithZeroOps α] [IsGroupWithZero α]

def toUnit? (x: α) (h: x ≠ 0 := by invert_tactic) : Units α where
  val := x
  inv := x⁻¹?
  val_mul_inv := mul_inv?_cancel _ _
  inv_mul_val := inv?_mul_cancel _ _

def toUnit?_one : toUnit? (1: α) = 1 := Units.val_inj.mp rfl

def npow?_eq_toUnit?_npow (a: α) (n: ℕ) (h: a ≠ 0) : toUnit? (a ^ n) = (toUnit? a) ^ n := Units.val_inj.mp rfl

def inv?_eq_toUnit?_inv (a: α) (h: a ≠ 0) : toUnit? (a⁻¹?) = (toUnit? a)⁻¹ := Units.val_inj.mp rfl

def zpow?_eq_toUnit?_zpow (a: α) (n: ℤ) (h: a ≠ 0) : toUnit? (a ^? n) = (toUnit? a) ^ n := by
  cases n using Int.coe_cases with
  | ofNat n =>
    conv => { lhs; lhs; rw [zpow?_ofNat] }
    rw [npow?_eq_toUnit?_npow]
    rfl
  | negSucc n =>
    conv => { lhs; lhs; rw [zpow?_negSucc _ _ (by invert_tactic)] }
    rw [npow?_eq_toUnit?_npow, inv?_eq_toUnit?_inv]
    rfl

def mul_eq_toUnit?_mul (a b: α) (ha: a ≠ 0) (hb: b ≠ 0) :
  toUnit? (a * b) = toUnit? a * toUnit? b := Units.val_inj.mp rfl

def div_eq_toUnit?_div (a b: α) (ha: a ≠ 0) (hb: b ≠ 0) : toUnit? (a /? b) (by
    intro h
    rw [div?_eq_mul_inv?] at h
    have := inv?_ne_zero b hb
    cases of_mul_eq_zero h <;> contradiction) = toUnit? a / toUnit? b := by
    rw [div_eq_mul_inv, ←inv?_eq_toUnit?_inv, ←mul_eq_toUnit?_mul]
    congr
    rw [div?_eq_mul_inv?]

def checked_zpow_pos_add (a: α) (n m: ℤ) (hn: a ≠ 0 ∨ 0 ≤ n) (hm: a ≠ 0 ∨ 0 ≤ m) : a ≠ 0 ∨ 0 ≤ n + m := by
  cases hn
  left; assumption
  cases hm
  left; assumption
  right
  apply Int.add_nonneg <;> assumption

macro_rules
| `(tactic|int_pow_tactic_trivial) => `(tactic|apply checked_zpow_pos_add <;> int_pow_tactic)

def zpow?_add (n m: ℤ) (a: α) (hn: a ≠ 0 ∨ 0 ≤ n) (hm: a ≠ 0 ∨ 0 ≤ m) :
  a ^? (n + m) = a ^? n * a ^? m := by
    by_cases h:a = 0
    · subst a
      repeat rw [zero_zpow?]
      by_cases hn':n = 0
      rw [if_pos hn']
      by_cases hm:m = 0
      rw [if_pos, if_pos hm]
      rw [mul_one]
      rw [hn', hm]; rfl
      rw [if_neg, if_neg, mul_zero]
      assumption
      rw [hn', Int.zero_add]; assumption
      rw [if_neg, if_neg, zero_mul]
      assumption
      intro h
      rw [Int.add_comm] at h
      replace h := Int.neg_eq_of_add_eq_zero h
      have : m < 0 := by
        rw [←Int.neg_neg m]
        apply Int.neg_lt_of_neg_lt
        rw [Int.neg_zero, h]
        apply Int.lt_iff_le_not_le.mpr
        have : 0 ≤ n := by
          apply hn.resolve_left
          intro; contradiction
        apply And.intro
        assumption
        intro g
        have := Int.le_antisymm g this
        contradiction
      cases hm
      contradiction
      have := Int.not_le_of_gt this
      contradiction
      apply hm.resolve_left
      intro; contradiction
      apply hn.resolve_left
      intro; contradiction
      apply Int.add_nonneg
      apply hn.resolve_left
      intro; contradiction
      apply hm.resolve_left
      intro; contradiction
    · apply (Units.val_inj (a := toUnit? _) (b := toUnit? _)).mpr
      rw [mul_eq_toUnit?_mul]
      repeat rw [zpow?_eq_toUnit?_zpow (α := α)]
      rw [zpow_add]
      assumption

def zpow?_sub (n m: ℤ) (a: α) (hn: a ≠ 0) :
  a ^? (n - m) = a ^? n /? a ^? m := by
  apply (Units.val_inj (a := toUnit? _) (b := toUnit? _ _)).mpr
  rw [div_eq_toUnit?_div]
  repeat rw [zpow?_eq_toUnit?_zpow (α := α)]
  rw [zpow_sub]
  assumption

def inv?_eq_of_mul_left (a b: α) (h: a * b = 1) : a⁻¹?~(by
  intro g; rw [g, zero_mul] at h
  exact zero_ne_one _ h) = b := by
  apply (Units.val_inj (a := toUnit? _) (b := toUnit? _ _)).mpr
  rw [inv?_eq_toUnit?_inv]
  apply inv_eq_of_mul_left
  rw [←mul_eq_toUnit?_mul, ←toUnit?_one]
  congr
  intro g
  rw [g, mul_zero] at h
  exact zero_ne_one _ h

def inv?_eq_of_mul_right (a b: α) (h: b * a = 1) : b = a⁻¹?~(by
  intro g; rw [g, mul_zero] at h
  exact zero_ne_one _ h) := by
  apply (Units.val_inj (a := toUnit? _ _) (b := toUnit? _)).mpr
  rw [inv?_eq_toUnit?_inv]
  apply inv_eq_of_mul_right
  rw [←mul_eq_toUnit?_mul, ←toUnit?_one]
  congr
  intro g
  rw [g, zero_mul] at h
  exact zero_ne_one _ h

def inv?_inv? (a: α) (h: a ≠ 0) : a⁻¹?⁻¹? = a := by
  symm
  refine inv?_eq_of_mul_right a⁻¹? a ?_
  rw [mul_inv?_cancel]

def div?_mul_cancel (a b: α) (h: b ≠ 0) : a /? b * b = a := by
  rw [div?_eq_mul_inv?, mul_assoc, inv?_mul_cancel, mul_one]

def mul_div?_cancel [IsCommMagma α] (a b: α) (h: b ≠ 0) : b * (a /? b) = a := by
  rw [div?_eq_mul_inv?, mul_left_comm, mul_inv?_cancel, mul_one]

def of_mul_right_nonzero (a b k: α) (hk: k ≠ 0) : a * k = b * k -> a = b := by
  intro h
  rw [←mul_one a, ←mul_one b, ←mul_inv?_cancel k, ←mul_assoc, ←mul_assoc, h]
  assumption

def of_mul_left_nonzero (a b k: α) (hk: k ≠ 0) : k * a = k * b -> a = b :=by
  intro h
  rw [←one_mul a, ←one_mul b, ←inv?_mul_cancel k, mul_assoc, mul_assoc, h]
  assumption
