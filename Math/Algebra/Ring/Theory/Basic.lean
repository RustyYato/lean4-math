import Math.Algebra.Ring.Defs
import Math.Algebra.Group.Hom

structure Ring (α: Type*) where
  [ops: RingOps α]
  [spec: IsRing α]

namespace Ring

@[coe]
def Elem (_: Ring α) := α

instance : CoeSort (Ring α) (Type _) := ⟨Elem⟩

instance (r: Ring α) : RingOps r := r.ops
instance (r: Ring α) : IsRing r := r.spec

def opp (r: Ring α) : Ring αᵐᵒᵖ :=
  let _ := r.ops
  have := r.spec
  Ring.mk

set_option linter.unusedVariables false in
def ofMinimalAxioms
  (zero: α)
  (one: α)
  (neg: α -> α)
  (add: α -> α -> α)
  (mul: α -> α -> α) :
  let _ : One α := ⟨one⟩
  let _ : Zero α := ⟨zero⟩
  let _ : Neg α := ⟨neg⟩
  let _ : Add α := ⟨add⟩
  let _ : Mul α := ⟨mul⟩
  ∀(add_comm: ∀(a b: α), a + b = b + a)
   (add_assoc: ∀(a b c: α), a + b + c = a + (b + c))
   (mul_assoc: ∀(a b c: α), a * b * c = a * (b * c))
   (zero_add: ∀(a: α), 0 + a = a)
   (neg_add_cancel: ∀(a: α), -a + a = 0)
   (one_mul: ∀(a: α), 1 * a = a)
   (mul_one: ∀(a: α), a * 1 = a)
   (mul_add: ∀(k a b: α), k * (a + b) = k * a + k * b)
   (add_mul: ∀(a b k: α), (a + b) * k = a * k + b * k), Ring α :=
    let _ : One α := ⟨one⟩
    let _ : Zero α := ⟨zero⟩
    let _ : Neg α := ⟨neg⟩
    let _ : Add α := ⟨add⟩
    let _ : Mul α := ⟨mul⟩
    fun add_comm add_assoc
      mul_assoc zero_add
      neg_add_cancel
      one_mul mul_one
      mul_add add_mul =>

    let ops₀ : MonoidOps α := {
        npow := flip npowRec
    }
    let ops₁ : AddMonoidOps α := {
        nsmul := nsmulRec
    }
    let ops₁ : AddMonoidWithOneOps α := {
      natCast := natCastRec
    }
    let ops : RingOps α := {
      sub a b := a + -b
      intCast := intCastRec
      zsmul := zsmulRec
    }

    have add_group : IsAddGroup α := {
      add_assoc := add_assoc
      zero_add := zero_add
      add_zero a := by
        rw [add_comm, zero_add]
      sub_eq_add_neg _ _ := rfl
      zsmul_ofNat _ _ := rfl
      zsmul_negSucc _ _ := rfl
      neg_add_cancel := neg_add_cancel
    }

    have monoid : IsMonoid α := {
      mul_assoc := mul_assoc
      one_mul := one_mul
      mul_one := mul_one
    }

    have : IsRing α := {
      add_group, monoid with
      add_comm:= add_comm
      left_distrib := mul_add
      right_distrib := add_mul
      natCast_zero := rfl
      natCast_succ _ := rfl
      zero_mul a := by
        have : (0 + 0) * a = 0 + (0: α) * a := by rw [add_zero, zero_add]
        rw [add_mul] at this
        exact add_right_cancel this
      mul_zero a := by
        have : a * (0 + 0) = 0 + a * (0: α) := by rw [add_zero, zero_add]
        rw [mul_add] at this
        exact add_right_cancel this
      intCast_ofNat _ := rfl
      intCast_negSucc _ := rfl
    }
    Ring.mk

end Ring
