import Math.Algebra.Ring
import Math.Function.Basic

structure Units (α: Type*) [One α] [Mul α] where
  val: α
  inv: α
  val_mul_inv: val * inv = 1
  inv_mul_val: inv * val = 1

instance [MonoidOps α] [IsMonoid α] : One (Units α) where
  one := {
    val := 1
    inv := 1
    val_mul_inv := one_mul _
    inv_mul_val := one_mul _
  }

instance [MonoidOps α] [IsMonoid α] : Mul (Units α) where
  mul a b := {
    val := a.val * b.val
    inv := b.inv * a.inv
    val_mul_inv := by
      rw [mul_assoc, ←mul_assoc b.val, b.val_mul_inv, one_mul, a.val_mul_inv]
    inv_mul_val := by
      rw [mul_assoc, ←mul_assoc a.inv, a.inv_mul_val, one_mul, b.inv_mul_val]
  }

instance [One α] [Mul α] : Inv (Units α) where
  inv a := {
    val := a.inv
    inv := a.val
    val_mul_inv := a.inv_mul_val
    inv_mul_val := a.val_mul_inv
  }

instance [MonoidOps α] [IsMonoid α] : Pow (Units α) ℕ where
  pow a n := {
    val := a.val ^ n
    inv := a.inv ^ n
    val_mul_inv := by
      induction n with
      | zero => rw [npow_zero, npow_zero, one_mul]
      | succ n ih =>
        rw [npow_succ, npow_succ', mul_assoc, ←mul_assoc a.val, a.val_mul_inv, one_mul, ih]
    inv_mul_val := by
      induction n with
      | zero => rw [npow_zero, npow_zero, one_mul]
      | succ n ih =>
        rw [npow_succ, npow_succ', mul_assoc, ←mul_assoc a.inv, a.inv_mul_val, one_mul, ih]
  }

instance [MonoidOps α] [IsMonoid α] : Pow (Units α) ℤ where
  pow := flip zpowRec

instance [MonoidOps α] [IsMonoid α] : Div (Units α) where
  div := div'

def Units.val_inj [MonoidOps α] [IsMonoid α] : Function.Injective (Units.val (α := α)) := by
  intro a b eq
  cases a with | mk a a' aa' a'a =>
  cases b with | mk b b' bb' b'b =>
  congr
  dsimp at eq; subst b
  have : a' * (a * a') = a' * (a * b') := by rw [aa', bb']
  rw [←mul_assoc, ←mul_assoc, a'a, one_mul, one_mul] at this
  assumption

def Units.inv_inj [MonoidOps α] [IsMonoid α] : Function.Injective (Units.inv (α := α)) := by
  intro a b eq
  cases a with | mk a a' aa' a'a =>
  cases b with | mk b b' bb' b'b =>
  congr
  dsimp at eq; subst b'
  have : a * (a' * a) = a * (a' * b) := by rw [a'a, b'b]
  rw [←mul_assoc, ←mul_assoc, aa', one_mul, one_mul] at this
  assumption

instance [MonoidOps α] [IsMonoid α] : IsGroup (Units α) where
  mul_assoc := by
    intro a b c
    apply Units.val_inj
    apply mul_assoc
  one_mul := by
    intro a
    apply Units.val_inj
    apply one_mul
  mul_one := by
    intro a
    apply Units.val_inj
    apply mul_one
  div_eq_mul_inv _ _ := rfl
  zpow_ofNat _ _ := rfl
  zpow_negSucc _ _ := rfl
  inv_mul_cancel := by
    intro a
    apply Units.val_inj
    exact a.inv_mul_val
  npow_zero := by
    intro a
    apply Units.val_inj
    apply npow_zero
  npow_succ := by
    intro a n
    apply Units.val_inj
    apply npow_succ

structure AddUnits (α: Type*) [Zero α] [Add α] where
  val: α
  neg: α
  val_add_neg: val + neg = 0
  neg_add_val: neg + val = 0

instance [AddMonoidOps α] [IsAddMonoid α] : Zero (AddUnits α) where
  zero := {
    val := 0
    neg := 0
    val_add_neg := zero_add _
    neg_add_val := zero_add _
  }

instance [AddMonoidOps α] [IsAddMonoid α] : Add (AddUnits α) where
  add a b := {
    val := a.val + b.val
    neg := b.neg + a.neg
    val_add_neg := by
      rw [add_assoc, ←add_assoc b.val, b.val_add_neg, zero_add, a.val_add_neg]
    neg_add_val := by
      rw [add_assoc, ←add_assoc a.neg, a.neg_add_val, zero_add, b.neg_add_val]
  }

instance [Zero α] [Add α] : Neg (AddUnits α) where
  neg a := {
    val := a.neg
    neg := a.val
    val_add_neg := a.neg_add_val
    neg_add_val := a.val_add_neg
  }

instance [AddMonoidOps α] [IsAddMonoid α] : SMul ℕ (AddUnits α) where
  smul n a := {
    val := n • a.val
    neg := n • a.neg
    val_add_neg := by
      induction n with
      | zero => rw [zero_nsmul, zero_nsmul, zero_add]
      | succ n ih =>
        rw [succ_nsmul, succ_nsmul', add_assoc, ←add_assoc a.val, a.val_add_neg, zero_add, ih]
    neg_add_val := by
      induction n with
      | zero => rw [zero_nsmul, zero_nsmul, zero_add]
      | succ n ih =>
        rw [succ_nsmul, succ_nsmul', add_assoc, ←add_assoc a.neg, a.neg_add_val, zero_add, ih]
  }

instance [AddMonoidOps α] [IsAddMonoid α] : SMul ℤ (AddUnits α) where
  smul := zsmulRec

instance [AddMonoidOps α] [IsAddMonoid α] : Sub (AddUnits α) where
  sub := sub'

def AddUnits.val_inj [AddMonoidOps α] [IsAddMonoid α] : Function.Injective (AddUnits.val (α := α)) := by
  intro a b eq
  cases a with | mk a a' aa' a'a =>
  cases b with | mk b b' bb' b'b =>
  congr
  dsimp at eq; subst b
  have : a' + (a + a') = a' + (a + b') := by rw [aa', bb']
  rw [←add_assoc, ←add_assoc, a'a, zero_add, zero_add] at this
  assumption

def AddUnits.neg_inj [AddMonoidOps α] [IsAddMonoid α] : Function.Injective (AddUnits.neg (α := α)) := by
  intro a b eq
  cases a with | mk a a' aa' a'a =>
  cases b with | mk b b' bb' b'b =>
  congr
  dsimp at eq; subst b'
  have : a + (a' + a) = a + (a' + b) := by rw [a'a, b'b]
  rw [←add_assoc, ←add_assoc, aa', zero_add, zero_add] at this
  assumption

instance [AddMonoidOps α] [IsAddMonoid α] : IsAddGroup (AddUnits α) where
  add_assoc := by
    intro a b c
    apply AddUnits.val_inj
    apply add_assoc
  zero_add := by
    intro a
    apply AddUnits.val_inj
    apply zero_add
  add_zero := by
    intro a
    apply AddUnits.val_inj
    apply add_zero
  sub_eq_add_neg _ _ := rfl
  zsmul_ofNat _ _ := rfl
  zsmul_negSucc _ _ := rfl
  neg_add_cancel := by
    intro a
    apply AddUnits.val_inj
    exact a.neg_add_val
  zero_nsmul := by
    intro a
    apply AddUnits.val_inj
    apply zero_nsmul
  succ_nsmul := by
    intro a n
    apply AddUnits.val_inj
    apply succ_nsmul
