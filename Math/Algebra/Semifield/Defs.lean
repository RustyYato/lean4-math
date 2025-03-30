import Math.Algebra.Semiring.Defs
import Math.Algebra.GroupWithZero.Defs

class SemifieldOps (α: Type*) extends SemiringOps α, GroupWithZeroOps α where

instance (priority := 50) [SemiringOps α] [CheckedIntPow? α] [CheckedInv? α] [CheckedDiv? α] : SemifieldOps α where

def zpow?Rec [SemiringOps α] [CheckedInv? α] (a: α) (n: ℤ) (h: a ≠ 0 ∨ 0 ≤ n) : α :=
  match n with
  | .ofNat n => a ^ n
  | .negSucc n => (a⁻¹? ~(by
    apply h.resolve_right
    apply Int.not_le.mpr
    apply Int.negSucc_lt_zero)) ^ n.succ

class IsNonCommSemifield (α: Type*) [SemifieldOps α] : Prop extends IsSemiring α, IsGroupWithZero α where
class IsSemifield (α: Type*) [SemifieldOps α] : Prop extends IsNonCommSemifield α, IsCommMagma α  where

instance [SemifieldOps α] [h: IsSemiring α] [g: IsGroupWithZero α] : IsNonCommSemifield α := { h, g with }
instance [SemifieldOps α] [IsNonCommSemifield α] [IsCommMagma α] : IsSemifield α := {  }

variable [SemifieldOps α] [IsNonCommSemifield α]

def add_div?_add' [SemifieldOps α] [IsNonCommSemifield α] (a b c: α) (h: c ≠ 0) : a /? c + b /? c = (a + b) /? c := by
  rw [div?_eq_mul_inv?, div?_eq_mul_inv?, div?_eq_mul_inv?, ←add_mul]

def div?_self [SemifieldOps α] [IsNonCommSemifield α] (a: α) (h: a ≠ 0) : a /? a = 1 := by
  rw [div?_eq_mul_inv?, mul_inv?_cancel]

instance [SemifieldOps α] [IsNonCommSemifield α] : IsMulCancel₀ α where
  mul_left_cancel₀ := by
    intro a b k hk h
    have : k⁻¹? * (k * a) = k⁻¹? * (k * b) := by rw [h]
    rwa [←mul_assoc, ←mul_assoc, inv?_mul_cancel,
      one_mul, one_mul] at this
  mul_right_cancel₀ := by
    intro a b k hk h
    have : (a * k) * k⁻¹? = (b * k) * k⁻¹? := by rw [h]
    rwa [mul_assoc, mul_assoc, mul_inv?_cancel,
      mul_one, mul_one] at this
