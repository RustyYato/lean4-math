import Math.Algebra.Monoid.Defs
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

def Units.val.inj [MonoidOps α] [IsMonoid α] : Function.Injective (Units.val (α := α)) := by
  intro a b eq
  cases a with | mk a a' aa' a'a =>
  cases b with | mk b b' bb' b'b =>
  congr
  dsimp at eq; subst b
  have : a' * (a * a') = a' * (a * b') := by rw [aa', bb']
  rw [←mul_assoc, ←mul_assoc, a'a, one_mul, one_mul] at this
  assumption

def Units.inv.inj [MonoidOps α] [IsMonoid α] : Function.Injective (Units.inv (α := α)) := by
  intro a b eq
  cases a with | mk a a' aa' a'a =>
  cases b with | mk b b' bb' b'b =>
  congr
  dsimp at eq; subst b'
  have : a * (a' * a) = a * (a' * b) := by rw [a'a, b'b]
  rw [←mul_assoc, ←mul_assoc, aa', one_mul, one_mul] at this
  assumption

def Units.val_inj [MonoidOps α] [IsMonoid α] {a b: Units α} : a.val = b.val ↔ a = b := Units.val.inj.eq_iff
def Units.inv_inj [MonoidOps α] [IsMonoid α] {a b: Units α} : a.inv = b.inv ↔ a = b := Units.inv.inj.eq_iff

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

def AddUnits.val.inj [AddMonoidOps α] [IsAddMonoid α] : Function.Injective (AddUnits.val (α := α)) := by
  intro a b eq
  cases a with | mk a a' aa' a'a =>
  cases b with | mk b b' bb' b'b =>
  congr
  dsimp at eq; subst b
  have : a' + (a + a') = a' + (a + b') := by rw [aa', bb']
  rw [←add_assoc, ←add_assoc, a'a, zero_add, zero_add] at this
  assumption

def AddUnits.neg.inj [AddMonoidOps α] [IsAddMonoid α] : Function.Injective (AddUnits.neg (α := α)) := by
  intro a b eq
  cases a with | mk a a' aa' a'a =>
  cases b with | mk b b' bb' b'b =>
  congr
  dsimp at eq; subst b'
  have : a + (a' + a) = a + (a' + b) := by rw [a'a, b'b]
  rw [←add_assoc, ←add_assoc, aa', zero_add, zero_add] at this
  assumption

def AddUnits.val_inj [AddMonoidOps α] [IsAddMonoid α] {a b: AddUnits α} : a.val = b.val ↔ a = b := AddUnits.val.inj.eq_iff
def AddUnits.neg_inj [AddMonoidOps α] [IsAddMonoid α] {a b: AddUnits α} : a.neg = b.neg ↔ a = b := AddUnits.neg.inj.eq_iff

class IsUnit {α: Type*} [One α] [Mul α] (x: α) where
  eq_unit: ∃u: Units α, u.val = x

namespace IsUnit

variable [One α] [Mul α]

private noncomputable
abbrev val (x: α) [h: IsUnit x] : α := (Classical.choose h.eq_unit).val

private
def val_eq (x: α) [h: IsUnit x] : val x = x := by
  conv => {
    rhs; rw [←Classical.choose_spec h.eq_unit]
  }

noncomputable
def inv (x: α) [h: IsUnit x] : α := (Classical.choose h.eq_unit).inv

def mul_inv (x: α) [h: IsUnit x] : x * inv x = 1 := by
  conv => { lhs; lhs; rw [←val_eq x] }
  exact (Classical.choose h.eq_unit).val_mul_inv

def inv_mul (x: α) [h: IsUnit x] : inv x * x = 1 := by
  conv => { lhs; rhs; rw [←val_eq x] }
  exact (Classical.choose h.eq_unit).inv_mul_val

end IsUnit

noncomputable
def toUnit (x: α) [One α] [Mul α] [IsUnit x] : Units α where
  val := x
  inv := IsUnit.inv x
  val_mul_inv := IsUnit.mul_inv x
  inv_mul_val := IsUnit.inv_mul x

instance : IsUnit (1: Nat) where
  eq_unit := ⟨⟨1, 1, rfl, rfl⟩, rfl⟩
instance : IsUnit (1: Int) where
  eq_unit := ⟨⟨1, 1, rfl, rfl⟩, rfl⟩
instance : IsUnit (-1: Int) where
  eq_unit := ⟨⟨-1, -1, rfl, rfl⟩, rfl⟩

def Nat.zeroNotUnit : ¬IsUnit 0 := by
  intro h
  have := h.mul_inv
  rw [Nat.zero_mul] at this
  contradiction
def Nat.addTwoNotUnit : ¬IsUnit (n + 2) := by
  intro h
  have := h.mul_inv
  rw [Nat.add_mul] at this
  generalize hy:IsUnit.inv (n + 2) = y
  rw [hy] at this
  cases y
  rw [Nat.mul_zero, Nat.mul_zero] at this; contradiction
  rw [Nat.mul_add 2, ←Nat.add_assoc] at this
  have := Nat.succ.inj this
  contradiction

macro_rules
| `(tactic|contradiction) => `(tactic|exfalso; apply Nat.zeroNotUnit; assumption)
macro_rules
| `(tactic|contradiction) => `(tactic|exfalso; apply Nat.addTwoNotUnit; assumption)

def Nat.ofIsUnit (x: Nat) [h: IsUnit x] : x = 1 := by
  match x, h with
  | 0, _ => contradiction
  | 1, _ => rfl
  | x + 2, _ => contradiction

def Int.ofIsUnit (x: Int) [h: IsUnit x] : x = 1 ∨ x = -1 := by
  suffices IsUnit x.natAbs by
    have := Nat.ofIsUnit x.natAbs
    rcases Int.natAbs_eq x with h | h
    rw [h, this]; left; rfl
    rw [h, this]; right; rfl
  obtain ⟨u, h⟩ := h
  refine ⟨⟨u.val.natAbs, u.inv.natAbs, ?_, ?_⟩, ?_⟩
  rw [←Int.natAbs_mul, u.val_mul_inv]; rfl
  rw [←Int.natAbs_mul, u.inv_mul_val]; rfl
  dsimp
  rw [h]
