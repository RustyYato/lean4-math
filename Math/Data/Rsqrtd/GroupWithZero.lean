import Math.Logic.Fact
import Math.Data.Rsqrtd.Ring
import Math.Algebra.Field.Defs

namespace Rsqrtd

variable {R: Type*} [FieldOps R] [IsField R] {d: R}

def NoSolution (d: R) : Prop := ∀r: R, r ^ 2 ≠ d

variable [Fact (NoSolution d)]

private def getNoSolution : NoSolution d := Fact.proof

def norm_ne_zero (x: R√d) (hx: x ≠ 0) : norm x ≠ 0 := by
  by_cases hb:x.b = 0
  · rw [norm_def, hb, zero_npow_succ, mul_zero, sub_zero]
    intro g
    apply hx
    ext
    rw [npow_two] at g
    cases of_mul_eq_zero g <;> assumption
    assumption
  intro g
  apply hx
  unfold norm at g
  replace g := eq_of_sub_eq_zero g
  have := getNoSolution (d := d) (x.a /? x.b)
  rw [npow_two, npow_two] at g
  rw [div?_eq_mul_inv?, npow_two,
    mul_assoc, mul_left_comm _ x.a, ←mul_assoc, g, mul_assoc,
    ←inv?_mul_rev, mul_inv?_cancel, mul_one] at this
  contradiction

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply norm_ne_zero <;> invert_tactic)

instance : CheckedInv? (R√d) where
  checked_invert x h := {
    a := x.a /? norm x
    b := -x.b /? norm x
  }

instance : CheckedDiv? (R√d) where
  checked_div a b h := a * b⁻¹?
instance : CheckedIntPow? (R√d) := instCheckedIntPow

@[simp] def a_inv (x: R√d) (h: x ≠ 0) : a (x⁻¹?) = (a x) /? norm x := rfl
@[simp] def b_inv (x: R√d) (h: x ≠ 0) : b (x⁻¹?) = (-b x) /? norm x := rfl

instance : IsGroupWithZero (R√d) where
  div?_eq_mul_inv? _ _ _ := rfl
  zpow?_ofNat _ _ := rfl
  zpow?_negSucc _ _ _ := rfl
  mul_inv?_cancel a h := by
    ext <;> simp
    rw [div?_eq_mul_inv?, div?_eq_mul_inv?,
      ←mul_assoc, ←mul_assoc,
      mul_neg, ←add_mul, ←sub_eq_add_neg,
      ←npow_two, mul_assoc, ←npow_two,
      ←norm_def, mul_inv?_cancel]
    rw [div?_eq_mul_inv?, div?_eq_mul_inv?, ←mul_assoc,
      ←mul_assoc, mul_neg, neg_mul, mul_comm a.a,
      neg_add_cancel]

end Rsqrtd
