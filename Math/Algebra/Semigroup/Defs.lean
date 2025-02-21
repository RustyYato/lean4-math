import Math.Type.Notation
import Math.Algebra.Notation
import Math.Algebra.AddMul
import Math.Relation.Basic
import Math.Logic.Nontrivial

variable [Add α] [Mul α] [Zero α] [One α]

class IsAddSemigroup (α: Type*) [Add α]: Prop where
  add_assoc (a b c: α) : a + b + c = a + (b + c)
class IsSemigroup (α: Type*) [Mul α]: Prop where
  mul_assoc (a b c: α) : a * b * c = a * (b * c)

def add_assoc [IsAddSemigroup α] : ∀(a b c: α), a + b + c = a + (b + c) := IsAddSemigroup.add_assoc
def mul_assoc [IsSemigroup α] : ∀(a b c: α), a * b * c = a * (b * c) := IsSemigroup.mul_assoc

instance [Mul α] [IsSemigroup α] : IsAddSemigroup (AddOfMul α) where
  add_assoc := mul_assoc (α := α)
instance [Add α] [IsAddSemigroup α] : IsSemigroup (MulOfAdd α) where
  mul_assoc := add_assoc (α := α)
instance [Mul α] [IsSemigroup α] : IsSemigroup αᵐᵒᵖ where
  mul_assoc _ _ _ := (mul_assoc (α := α) _ _ _).symm

class IsAddCommMagma (α: Type*) [Add α]: Prop where
  add_comm (a b: α) : a + b = b + a
class IsCommMagma (α: Type*) [Mul α]: Prop where
  mul_comm (a b: α) : a * b = b * a

def add_comm [IsAddCommMagma α] : ∀(a b: α), a + b = b + a := IsAddCommMagma.add_comm
def mul_comm [IsCommMagma α] : ∀(a b: α), a * b = b * a := IsCommMagma.mul_comm

instance [Mul α] [IsCommMagma α] : IsAddCommMagma (AddOfMul α) where
  add_comm := mul_comm (α := α)
instance [Add α] [IsAddCommMagma α] : IsCommMagma (MulOfAdd α) where
  mul_comm := add_comm (α := α)
instance [Add α] [IsAddCommMagma α] : IsAddCommMagma αᵐᵒᵖ :=
  inferInstanceAs (IsAddCommMagma α)
instance [Mul α] [IsCommMagma α] : IsCommMagma αᵐᵒᵖ where
  mul_comm _ _ := mul_comm (α := α) _ _

def add_comm_left [Add α] [IsAddSemigroup α] [IsAddCommMagma α]
  (a b c: α) : a + b + c = c + b + a := by
  rw [add_comm _ c, add_comm a, add_assoc]

def add_comm_right [Add α] [IsAddSemigroup α] [IsAddCommMagma α]
  (a b c: α) : a + b + c = a + c + b := by
  rw [add_assoc, add_comm b, add_assoc]

def add_left_comm [Add α] [IsAddSemigroup α] [IsAddCommMagma α]
  (a b c: α) : a + (b + c) = b + (a + c) := by
  rw [←add_assoc, ←add_assoc, add_comm b]

def add_right_comm [Add α] [IsAddSemigroup α] [IsAddCommMagma α]
  (a b c: α) : a + (b + c) = c + (b + a) := by
  rw [←add_assoc, ←add_assoc, add_comm_left]

def mul_comm_left [Mul α] [IsSemigroup α] [IsCommMagma α]
  (a b c: α) : a * b * c = c * b * a := add_comm_left (α := AddOfMul α) _ _ _

def mul_comm_right [Mul α] [IsSemigroup α] [IsCommMagma α]
  (a b c: α) : a * b * c = a * c * b := add_comm_right (α := AddOfMul α) _ _ _

def mul_left_comm [Mul α] [IsSemigroup α] [IsCommMagma α]
  (a b c: α) : a * (b * c) = b * (a * c) := add_left_comm (α := AddOfMul α) _ _ _

def mul_right_comm [Mul α] [IsSemigroup α] [IsCommMagma α]
  (a b c: α) : a * (b * c) = c * (b * a) := add_right_comm (α := AddOfMul α) _ _ _

class IsAddLeftCancel (α: Type*) [Add α]: Prop where
  add_left_cancel {a b k: α}: k + a = k + b -> a = b
class IsAddRightCancel (α: Type*) [Add α]: Prop where
  add_right_cancel {a b k: α}: a + k = b + k -> a = b

class IsLeftCancel (α: Type*) [Mul α]: Prop where
  mul_left_cancel {a b k: α}: k * a = k * b -> a = b
class IsRightCancel (α: Type*) [Mul α]: Prop where
  mul_right_cancel {a b k: α}: a * k = b * k -> a = b

class IsAddCancel (α: Type*) [Add α] extends IsAddLeftCancel α, IsAddRightCancel α: Prop
class IsMulCancel (α: Type*) [Mul α] extends IsLeftCancel α, IsRightCancel α: Prop

instance [Add α] [IsAddLeftCancel α] [IsAddRightCancel α] : IsAddCancel α where
instance [Mul α] [IsLeftCancel α] [IsRightCancel α] : IsMulCancel α where

def add_left_cancel [IsAddLeftCancel α] {a b k: α}: k + a = k + b -> a = b := IsAddLeftCancel.add_left_cancel
def add_right_cancel [IsAddRightCancel α] {a b k: α}: a + k = b + k -> a = b := IsAddRightCancel.add_right_cancel
def mul_left_cancel [IsLeftCancel α] {a b k: α}: k * a = k * b -> a = b := IsLeftCancel.mul_left_cancel
def mul_right_cancel [IsRightCancel α] {a b k: α}: a * k = b * k -> a = b := IsRightCancel.mul_right_cancel

instance [Mul α] [IsLeftCancel α] : IsAddLeftCancel (AddOfMul α) where
  add_left_cancel := mul_left_cancel (α := α)
instance [Mul α] [IsRightCancel α] : IsAddRightCancel (AddOfMul α) where
  add_right_cancel := mul_right_cancel (α := α)

instance [Add α] [IsAddLeftCancel α] : IsLeftCancel (MulOfAdd α) where
  mul_left_cancel := add_left_cancel (α := α)
instance [Add α] [IsAddRightCancel α] : IsRightCancel (MulOfAdd α) where
  mul_right_cancel := add_right_cancel (α := α)

instance (priority := 50) IsAddCommMagma.toLeftCancel [Add α] [IsAddCommMagma α] [IsAddRightCancel α] : IsAddLeftCancel α where
  add_left_cancel {a b k} := by
    rw [add_comm k, add_comm k]
    exact add_right_cancel

instance (priority := 50) IsAddCommMagma.toRightCancel [Add α] [IsAddCommMagma α] [IsAddLeftCancel α] : IsAddRightCancel α where
  add_right_cancel {a b k} := by
    rw [add_comm _ k, add_comm _ k]
    exact add_left_cancel

instance (priority := 50) IsCommMagma.toLeftCancel [Mul α] [IsCommMagma α] [IsRightCancel α] : IsLeftCancel α where
  mul_left_cancel :=
    add_left_cancel (α := AddOfMul α)

instance (priority := 50) IsCommMagma.toRightCancel [Mul α] [IsCommMagma α] [IsLeftCancel α] : IsRightCancel α where
  mul_right_cancel := add_right_cancel (α := AddOfMul α)

class IsAddZeroClass (α: Type*) [Add α] [Zero α]: Prop where
  zero_add (a: α): 0 + a = a
  add_zero (a: α): a + 0 = a
class IsMulOneClass (α: Type*) [Mul α] [One α]: Prop where
  one_mul (a: α): 1 * a = a
  mul_one (a: α): a * 1 = a
class IsMulZeroClass (α: Type*) [Mul α] [Zero α]: Prop where
  zero_mul (a: α): 0 * a = 0
  mul_zero (a: α): a * 0 = 0

@[simp] def zero_add [IsAddZeroClass α] (a: α): 0 + a = a := IsAddZeroClass.zero_add a
@[simp] def add_zero [IsAddZeroClass α] (a: α): a + 0 = a := IsAddZeroClass.add_zero a
@[simp] def zero_mul [IsMulZeroClass α] (a: α): 0 * a = 0 := IsMulZeroClass.zero_mul a
@[simp] def mul_zero [IsMulZeroClass α] (a: α): a * 0 = 0 := IsMulZeroClass.mul_zero a
@[simp] def one_mul [IsMulOneClass α] (a: α): 1 * a = a := IsMulOneClass.one_mul a
@[simp] def mul_one [IsMulOneClass α] (a: α): a * 1 = a := IsMulOneClass.mul_one a

instance [Mul α] [One α] [IsMulOneClass α] : IsAddZeroClass (AddOfMul α) where
  add_zero := mul_one (α := α)
  zero_add := one_mul (α := α)
instance [Add α] [Zero α] [IsAddZeroClass α] : IsMulOneClass (MulOfAdd α) where
  mul_one := add_zero (α := α)
  one_mul := zero_add (α := α)
instance [Add α] [Zero α] [IsAddZeroClass α] : IsAddZeroClass αᵐᵒᵖ :=
  inferInstanceAs (IsAddZeroClass α)
instance [Mul α] [One α] [IsMulOneClass α] : IsMulOneClass αᵐᵒᵖ where
  one_mul := mul_one (α := α)
  mul_one := one_mul (α := α)
instance [Mul α] [Zero α] [IsMulZeroClass α] : IsMulZeroClass αᵐᵒᵖ where
  zero_mul := mul_zero (α := α)
  mul_zero := zero_mul (α := α)

def IsAddZeroClass.ofAddCommMagma [Add α] [Zero α] [IsAddCommMagma α] (h: ∀x: α, 0 + x = x) : IsAddZeroClass α where
  zero_add := h
  add_zero x := by rw [add_comm]; apply h

def IsMulZeroClass.ofCommMagma [Mul α] [Zero α] [IsCommMagma α] (h: ∀x: α, 0 * x = 0) : IsMulZeroClass α where
  zero_mul := h
  mul_zero x := by rw [mul_comm]; apply h

def IsMulOneClass.ofCommMagma [Mul α] [One α] [IsCommMagma α] (h: ∀x: α, 1 * x = x) : IsMulOneClass α where
  one_mul := h
  mul_one x := by rw [mul_comm]; apply h

def all_eq_zero_of_trivial [Mul α] [Zero α] [One α] [IsMulZeroClass α] [IsMulOneClass α] (triv: (0: α) = (1: α)) (a: α) : a = 0 := by
  rw [←mul_one a, ←triv, mul_zero]

def subsingleton_of_trivial [Mul α] [Zero α] [One α] [IsMulZeroClass α] [IsMulOneClass α] (triv: (0: α) = (1: α)) : Subsingleton α where
  allEq a b := by
    rw [all_eq_zero_of_trivial triv a, all_eq_zero_of_trivial triv b]

instance [IsNontrivial α] [Mul α] [Zero α] [One α] [IsMulZeroClass α] [IsMulOneClass α] : NeZero (1: α) where
  out := by
    intro h
    have := Subsingleton.iff_not_nontrivial.mp (subsingleton_of_trivial h.symm)
    contradiction

def zero_ne_one (α: Type*) [IsNontrivial α] [Mul α] [Zero α] [One α] [IsMulZeroClass α] [IsMulOneClass α] : 0 ≠ (1: α) := Ne.symm (NeZero.ne (1: α))

instance (priority := 100) [Add α] [IsAddSemigroup α] : @Std.Associative α (· + ·) where
  assoc := add_assoc
instance (priority := 100) [Mul α] [IsSemigroup α] : @Std.Associative α (· * ·) where
  assoc := mul_assoc

instance (priority := 100) [Add α] [IsAddCommMagma α] : @Std.Commutative α (· + ·) where
  comm := add_comm
instance (priority := 100) [Mul α] [IsCommMagma α] : @Std.Commutative α (· * ·) where
  comm := mul_comm
