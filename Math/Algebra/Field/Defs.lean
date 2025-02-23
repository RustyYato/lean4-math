import Math.Algebra.Ring.Defs
import Math.Algebra.GroupWithZero.Defs

class FieldOps (α: Type*) extends RingOps α, GroupWithZeroOps α where

instance [h: RingOps α] [CheckedIntPow? α] [CheckedInv? α] [CheckedDiv? α] : FieldOps α where

def zpow?Rec [RingOps α] [CheckedInv? α] (a: α) (n: ℤ) (h: a ≠ 0 ∨ 0 ≤ n) : α :=
  match n with
  | .ofNat n => a ^ n
  | .negSucc n => (a⁻¹? ~(by
    apply h.resolve_right
    apply Int.not_le.mpr
    apply Int.negSucc_lt_zero)) ^ n.succ

class IsNonCommField (α: Type*) [FieldOps α] extends IsRing α, IsGroupWithZero α: Prop where
class IsField (α: Type*) [FieldOps α] extends IsNonCommField α, IsCommMagma α : Prop where

instance [FieldOps α] [h: IsRing α] [g: IsGroupWithZero α] : IsNonCommField α := { h, g with }
instance [FieldOps α] [IsNonCommField α] [IsCommMagma α] : IsField α := {  }

instance [FieldOps α] [IsNonCommField α] : NoZeroDivisors α where
  of_mul_eq_zero {a b} h := by
    apply Classical.or_iff_not_imp_right.mpr
    intro g
    have : (a * b) * b⁻¹? = 0 := by rw [h, zero_mul]
    rw [mul_assoc, mul_inv?_cancel, mul_one] at this
    assumption

def add_div?_add' [FieldOps α] [IsNonCommField α] (a b c: α) (h: c ≠ 0) : a /? c + b /? c = (a + b) /? c := by
  rw [div?_eq_mul_inv?, div?_eq_mul_inv?, div?_eq_mul_inv?, ←add_mul]

def div?_self [FieldOps α] [IsNonCommField α] (a: α) (h: a ≠ 0) : a /? a = 1 := by
  rw [div?_eq_mul_inv?, mul_inv?_cancel]
