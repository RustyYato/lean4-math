import Math.Algebra.Monoid.Defs
import Math.Ops.Checked
import Math.Data.Int.Basic

def of_npow_eq_zero [Zero α] [MonoidOps α] [IsMonoid α] [IsNontrivial α] [IsMulZeroClass α] [NoZeroDivisors α] (a: α) (n: ℕ) : a ^ n = 0 -> a = 0 := by
  induction n with
  | zero =>
    rw [npow_zero]
    intro h
    have := zero_ne_one _ h.symm; contradiction
  | succ n ih =>
    rw [npow_succ]
    intro h
    cases of_mul_eq_zero h
    apply ih
    assumption
    assumption

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply (zero_ne_one _).symm)

def mul_ne_zero [Mul α] [Zero α] [NoZeroDivisors α] (a b: α) (ha: a ≠ 0) (hb: b ≠ 0) : a * b ≠ 0 := by
  intro g
  cases of_mul_eq_zero g <;> contradiction

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply mul_ne_zero <;> invert_tactic)

def instCheckedIntPow [MonoidOps α] [Zero α] [CheckedInv? α] : CheckedIntPow? α where
  checked_pow a := fun
    | .ofNat n, h => a ^ n
    | .negSucc n, h =>
      have : a ≠ 0 := h.resolve_right (by
        intro g
        contradiction)
      a⁻¹? ^ n.succ

class GroupWithZeroOps (α: Type*) extends
  MonoidOps α,
  Zero α,
  CheckedIntPow? α,
  CheckedInv? α,
  CheckedDiv? α where

instance
  (priority := 100)
  [MonoidOps α]
  [Zero α] [CheckedIntPow? α]
  [CheckedInv? α] [CheckedDiv? α] :
  GroupWithZeroOps α where

class IsGroupWithZero (α: Type*) [GroupWithZeroOps α] extends IsMonoid α, IsMulZeroClass α, IsNontrivial α where
  mul_inv?_cancel: ∀(a: α) (h: a ≠ 0), a * a⁻¹? = 1
  div?_eq_mul_inv?: ∀(a b: α) (h: b ≠ 0), a /? b = a * b⁻¹?
  zpow?_ofNat (n: ℕ) (a: α) : a ^? (n: ℤ) = a ^ n
  zpow?_negSucc (n: ℕ) (a: α) (h: a ≠ 0) : a ^? (Int.negSucc n) = (a⁻¹? ^ n.succ)

variable [GroupWithZeroOps α] [IsGroupWithZero α]

def mul_inv?_cancel: ∀(a: α) (h: a ≠ 0), a * a⁻¹? = 1 := IsGroupWithZero.mul_inv?_cancel
def div?_eq_mul_inv?: ∀(a b: α) (h: b ≠ 0), a /? b = a * b⁻¹? := IsGroupWithZero.div?_eq_mul_inv?
def zpow?_ofNat (n: ℕ) (a: α) : a ^? (n: ℤ) = a ^ n := IsGroupWithZero.zpow?_ofNat _ _
def zpow?_negSucc (n: ℕ) (a: α) (h: a ≠ 0) : a ^? (Int.negSucc n) = (a⁻¹? ^ n.succ) := IsGroupWithZero.zpow?_negSucc _ _ _

instance [DecidableEq α] : NoZeroDivisors α where
  of_mul_eq_zero {a b} h := by
    apply Decidable.or_iff_not_imp_right.mpr
    intro g
    have : (a * b) * b⁻¹? = 0 := by rw [h, zero_mul]
    rw [mul_assoc, mul_inv?_cancel, mul_one] at this
    assumption

variable [NoZeroDivisors α]

def npow_ne_zero (a: α) (n: Nat) (h: a ≠ 0) : a ^ n ≠ 0 := by
  intro g
  have := of_npow_eq_zero _ _ g
  contradiction

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply npow_ne_zero; invert_tactic)

def inv?_ne_zero (a: α) (h: a ≠ 0) : a⁻¹? ≠ 0 := by
  intro g
  have : a * a⁻¹? = 0 := by rw [g, mul_zero]
  rw [mul_inv?_cancel] at this
  exact zero_ne_one _ this.symm

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply inv?_ne_zero)

def zpow?_ne_zero (a: α) (h: a ≠ 0) : a ^? n ≠ 0 := by
  intro g
  cases n using Int.coe_cases with
  | ofNat n =>
    rw [zpow?_ofNat] at g
    have := (of_npow_eq_zero _ _ g)
    contradiction
  | negSucc n =>
    rw [zpow?_negSucc] at g
    exact inv?_ne_zero _ _ (of_npow_eq_zero _ _ g)
    assumption

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply zpow?_ne_zero; try invert_tactic)

def zpow?_def (n: ℤ) (a: α) (h: a ≠ 0 ∨ 0 ≤ n) : a ^? n = if g:0 ≤ n then
      a ^ n.natAbs
    else
      (a⁻¹? ~(by
        apply h.resolve_right
        assumption)) ^ n.natAbs := by
    cases n using Int.coe_cases with
    | ofNat =>
      rw [zpow?_ofNat, dif_pos]
      rfl
      apply Int.ofNat_nonneg
    | negSucc n =>
      rw [dif_neg, zpow?_negSucc]
      rfl
      apply (Int.negSucc_not_nonneg _).mp

def inv?_rw_proof (a: α) (h g: a ≠ 0) : a⁻¹? ~(h) = a⁻¹? ~(g) := rfl
def zpow?_rw_proof (a: α) (n: ℤ) (h g: a ≠ 0 ∨ 0 ≤ n) : a ^? n ~(h) = a ^? n ~(g) := rfl

def inv?_mul_cancel (a: α) (h: a ≠ 0) : a⁻¹? * a = 1 := by
  conv => { lhs; rhs; rw [←mul_one a] }
  rw [←mul_inv?_cancel (a⁻¹?), ←mul_assoc a, mul_inv?_cancel, one_mul, mul_inv?_cancel]
  apply inv?_ne_zero

def mul_left_cancel' (a b k: α) (hk: k ≠ 0):
  k * a = k * b -> a = b := by
  intro h
  have : k⁻¹? * (k * a) = k⁻¹? * (k * b) := by rw [h]
  rw [←mul_assoc, ←mul_assoc, inv?_mul_cancel, one_mul, one_mul] at this
  assumption

def mul_right_cancel' (a b k: α) (hk: k ≠ 0):
  a * k = b * k -> a = b := by
  intro h
  have : (a * k) * k⁻¹? = (b * k) * k⁻¹? := by rw [h]
  rw [mul_assoc, mul_assoc, mul_inv?_cancel, mul_one, mul_one] at this
  assumption

def inv?_mul_rev (a b: α) (ha: a ≠ 0) (hb: b ≠ 0) :
  (a * b)⁻¹? = b⁻¹? * a⁻¹? := by
  apply mul_left_cancel' _ _ (a * b)
  invert_tactic
  rw [mul_inv?_cancel, ←mul_assoc, mul_assoc a, mul_inv?_cancel, mul_one, mul_inv?_cancel]

def zpow?_negSucc' (n: ℕ) (a: α) (h: a ≠ 0) : a ^? (Int.negSucc n) = (a ^ n.succ)⁻¹? := by
  rw [zpow?_negSucc _ _ h]
  induction n with
  | zero =>
    rw [npow_one]
    congr
    rw [npow_one]
  | succ n ih =>
    conv => {
      rhs; arg 1
      rw [npow_succ']
    }
    rw [npow_succ, ih, inv?_mul_rev]

def zero_zpow? (n: ℤ) (hn: 0 ≤ n) : (0: α) ^? n = if n = 0 then 1 else 0 := by
  cases n using Int.coe_cases with
  | negSucc n => contradiction
  | ofNat n =>
    rw [zpow?_ofNat]
    cases n
    rw [npow_zero, if_pos]
    rfl
    rw [npow_succ, mul_zero, if_neg]
    intro h
    have := Int.ofNat.inj h
    contradiction

def inv?_npow (a: α) (h: a ≠ 0) (n: ℕ) : (a⁻¹?) ^ n = (a ^ n)⁻¹? := by
  apply mul_left_cancel' (k := a^n) (a := _)
  invert_tactic
  rw [mul_inv?_cancel]
  induction n with
  | zero => rw [npow_zero, npow_zero, mul_one]
  | succ n ih =>
    rw [npow_succ, npow_succ', mul_assoc, ←mul_assoc a, mul_inv?_cancel, one_mul, ih]

def div?_npow [IsCommMagma α] (a b: α) (h: b ≠ 0) (n: ℕ) : (a /? b) ^ n = (a ^ n) /? (b ^ n) := by
  rw [div?_eq_mul_inv?, div?_eq_mul_inv?, mul_npow, inv?_npow]

def div?_self (a: α) (ha: a ≠ 0) : a /? a = 1 := by
  rw [div?_eq_mul_inv?, mul_inv?_cancel]

class IsLeftCancel₀ (α: Type*) [Mul α] [Zero α]: Prop where
  mul_left_cancel₀ {a b k: α}: k ≠ 0 -> k * a = k * b -> a = b
class IsRightCancel₀ (α: Type*) [Mul α] [Zero α]: Prop where
  mul_right_cancel₀ {a b k: α}: k ≠ 0 -> a * k = b * k -> a = b
class IsMulCancel₀ (α: Type*) [Mul α]  [Zero α]: Prop extends IsLeftCancel₀ α, IsRightCancel₀ α

def mul_left_cancel₀ [Mul α] [Zero α] [IsLeftCancel₀ α] {a b k: α}: k ≠ 0 -> k * a = k * b -> a = b := IsLeftCancel₀.mul_left_cancel₀
def mul_right_cancel₀ [Mul α] [Zero α] [IsRightCancel₀ α] {a b k: α}: k ≠ 0 -> a * k = b * k -> a = b := IsRightCancel₀.mul_right_cancel₀

instance : CheckedDiv? αᵐᵒᵖ where
  checked_div a b h := a * b⁻¹?

instance : IsGroupWithZero αᵐᵒᵖ where
  exists_ne := IsNontrivial.exists_ne (α := α)
  mul_inv?_cancel := inv?_mul_cancel (α := α)
  div?_eq_mul_inv? _ _ _ := rfl
  zpow?_ofNat := zpow?_ofNat (α := α)
  zpow?_negSucc := zpow?_negSucc (α := α)

instance (priority := 50) IsCommMagma.toLeftCancel₀ [Mul α] [Zero α] [IsCommMagma α] [IsRightCancel₀ α] : IsLeftCancel₀ α where
  mul_left_cancel₀ := by
    intro _ _ k
    rw [mul_comm k, mul_comm k]
    apply mul_right_cancel₀

instance (priority := 50) IsCommMagma.toRightCancel₀ [Mul α] [Zero α] [IsCommMagma α] [IsLeftCancel₀ α] : IsRightCancel₀ α where
  mul_right_cancel₀ := by
    intro _ _ k
    rw [mul_comm _ k, mul_comm _ k]
    apply mul_left_cancel₀

instance [Mul α] [Zero α] [IsLeftCancel₀ α] [IsRightCancel₀ α] : IsMulCancel₀ α where

instance : IsMulCancel₀ Nat where
  mul_left_cancel₀ := by
    intro a b k hk h
    apply Nat.mul_left_cancel _ h
    exact Nat.zero_lt_of_ne_zero hk
  mul_right_cancel₀ := by
    intro a b k hk h
    apply Nat.mul_right_cancel _ h
    exact Nat.zero_lt_of_ne_zero hk

instance : IsMulCancel₀ Int where
  mul_left_cancel₀ := by
    intro a b k hk h
    have : (k * a) / k = (k * b) / k := by rw [h]
    exact (Int.mul_eq_mul_left_iff hk).mp h
  mul_right_cancel₀ := by
    intro a b k hk h
    have : (a * k) / k = (b * k) / k := by rw [h]
    exact (Int.mul_eq_mul_right_iff hk).mp h
