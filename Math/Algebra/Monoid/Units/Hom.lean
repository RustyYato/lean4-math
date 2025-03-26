import Math.Algebra.Monoid.Hom
import Math.Algebra.Monoid.Units.Defs

def Units.lift
  [MonoidOps α] [IsMonoid α]
  [MonoidOps β] [IsMonoid β]
  (f: α →* β) : Units α →* Units β where
  toFun x := {
    val := f x.val
    inv := f x.inv
    val_mul_inv := by rw [←resp_mul, x.val_mul_inv, resp_one]
    inv_mul_val := by rw [←resp_mul, x.inv_mul_val, resp_one]
  }
  resp_one' := by
    apply Units.val_inj.mp
    apply resp_one
  resp_mul' {a b} := by
    apply Units.val_inj.mp
    apply resp_mul

def AddUnits.lift
  [AddMonoidOps α] [IsAddMonoid α]
  [AddMonoidOps β] [IsAddMonoid β]
  (f: α →+ β) : AddUnits α →+ AddUnits β where
  toFun x := {
    val := f x.val
    neg := f x.neg
    val_add_neg := by rw [←resp_add, x.val_add_neg, resp_zero]
    neg_add_val := by rw [←resp_add, x.neg_add_val, resp_zero]
  }
  resp_zero' := by
    apply AddUnits.val_inj.mp
    apply resp_zero
  resp_add' {a b} := by
    apply AddUnits.val_inj.mp
    apply resp_add
