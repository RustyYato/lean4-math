import Math.Type.Notation
import Math.Data.StdInt.Basic
import Math.AxiomBlame
import Math.Ops.Checked
import Math.Algebra.Notation
import Math.Algebra.AddMul

variable (α: Type*) [Zero α] [One α] [Add α] [Mul α] [Sub α] [Div α]
variable {α₀ α₁: Type*} [Zero α₀] [One α₁] [Add α₀] [Mul α₁] [Sub α₀] [Div α₁]
variable [Pow α ℕ] [Pow α₁ ℕ] [SMul ℕ α] [SMul ℕ α₀]
variable [Pow α ℤ] [Pow α₁ ℤ] [SMul ℤ α] [SMul ℤ α₀]
variable [Neg α] [Neg α₀] [Inv α] [Inv α₁]
variable [NatCast α] [IntCast α] [∀n, OfNat α (n+2)]

variable {R₀: Type*} [Zero R₀] [One R₀] [Add R₀] [Mul R₀] [Sub R₀] [Div R₀]
variable [Pow R₀ ℕ] [SMul ℕ R₀]
variable [Pow R₀ ℤ] [SMul ℤ R₀]
variable [Neg R₀] [Inv R₀]
variable [NatCast R₀] [IntCast R₀] [∀n, OfNat R₀ (n+2)]

variable {M₀: Type*} [Zero M₀] [Add M₀] [Sub M₀] [SMul ℕ M₀] [SMul ℤ M₀] [Neg M₀]
variable [SMul R₀ M₀]

variable (R: Type*) [Zero R] [One R] [Add R] [Mul R] [Sub R] [Div R]
variable [Pow R ℕ] [SMul ℕ R]
variable [Pow R ℤ] [SMul ℤ R]
variable [Neg R] [Inv R]
variable [NatCast R] [IntCast R] [∀n, OfNat R (n+2)]

variable (M: Type*) [Zero M] [Add M] [Sub M] [SMul ℕ M] [SMul ℤ M] [Neg M]
variable [SMul R M]

class IsNontrivial: Prop where
  zero_ne_one: 0 ≠ (1: α)

export IsNontrivial (zero_ne_one)

class IsAddSemigroup: Prop where
  add_assoc (a b c: α) : a + b + c = a + (b + c)
class IsSemigroup: Prop where
  mul_assoc (a b c: α) : a * b * c = a * (b * c)

export IsAddSemigroup (add_assoc)
export IsSemigroup (mul_assoc)

instance [IsSemigroup α] : IsAddSemigroup (AddOfMul α) where
  add_assoc := mul_assoc (α := α)
instance [IsAddSemigroup α] : IsSemigroup (MulOfAdd α) where
  mul_assoc := add_assoc (α := α)

class IsAddCommMagma: Prop where
  add_comm (a b: α) : a + b = b + a
class IsCommMagma: Prop where
  mul_comm (a b: α) : a * b = b * a

export IsAddCommMagma (add_comm)
export IsCommMagma (mul_comm)

instance [IsCommMagma α] : IsAddCommMagma (AddOfMul α) where
  add_comm := mul_comm (α := α)
instance [IsAddCommMagma α] : IsCommMagma (MulOfAdd α) where
  mul_comm := add_comm (α := α)

class IsAddLeftCancel: Prop where
  add_left_cancel {a b k: α}: k + a = k + b -> a = b
class IsAddRightCancel: Prop where
  add_right_cancel {a b k: α}: a + k = b + k -> a = b

class IsLeftCancel: Prop where
  mul_left_cancel {a b k: α}: k * a = k * b -> a = b
class IsRightCancel: Prop where
  mul_right_cancel {a b k: α}: a * k = b * k -> a = b

class IsAddCancel extends IsAddLeftCancel α, IsAddRightCancel α: Prop
class IsMulCancel extends IsLeftCancel α, IsRightCancel α: Prop

instance [IsAddLeftCancel α] [IsAddRightCancel α] : IsAddCancel α where
instance [IsLeftCancel α] [IsRightCancel α] : IsMulCancel α where

export IsAddLeftCancel (add_left_cancel)
export IsAddRightCancel (add_right_cancel)
export IsLeftCancel (mul_left_cancel)
export IsRightCancel (mul_right_cancel)

instance [IsLeftCancel α] : IsAddLeftCancel (AddOfMul α) where
  add_left_cancel := mul_left_cancel (α := α)
instance [IsRightCancel α] : IsAddRightCancel (AddOfMul α) where
  add_right_cancel := mul_right_cancel (α := α)

instance [IsAddLeftCancel α] : IsLeftCancel (MulOfAdd α) where
  mul_left_cancel := add_left_cancel (α := α)
instance [IsAddRightCancel α] : IsRightCancel (MulOfAdd α) where
  mul_right_cancel := add_right_cancel (α := α)

instance (priority := 50) IsAddCommMagma.toLeftCancel [IsAddCommMagma α] [IsAddRightCancel α] : IsAddLeftCancel α where
  add_left_cancel {a b k} := by
    rw [add_comm k, add_comm k]
    exact add_right_cancel

instance (priority := 50) IsAddCommMagma.toRightCancel [IsAddCommMagma α] [IsAddLeftCancel α] : IsAddRightCancel α where
  add_right_cancel {a b k} := by
    rw [add_comm _ k, add_comm _ k]
    exact add_left_cancel

instance (priority := 50) IsCommMagma.toLeftCancel [IsCommMagma α] [IsRightCancel α] : IsLeftCancel α where
  mul_left_cancel :=
    add_left_cancel (α := AddOfMul α)

instance (priority := 50) IsCommMagma.toRightCancel [IsCommMagma α] [IsLeftCancel α] : IsRightCancel α where
  mul_right_cancel := add_right_cancel (α := AddOfMul α)

class IsAddZeroClass: Prop where
  zero_add (a: α): 0 + a = a
  add_zero (a: α): a + 0 = a
class IsMulOneClass: Prop where
  one_mul (a: α): 1 * a = a
  mul_one (a: α): a * 1 = a
class IsMulZeroClass: Prop where
  zero_mul (a: α): 0 * a = 0
  mul_zero (a: α): a * 0 = 0

export IsAddZeroClass (zero_add add_zero)
export IsMulZeroClass (zero_mul mul_zero)
export IsMulOneClass (one_mul mul_one)

instance [IsMulOneClass α] : IsAddZeroClass (AddOfMul α) where
  add_zero := mul_one (α := α)
  zero_add := one_mul (α := α)
instance [IsAddZeroClass α] : IsMulOneClass (MulOfAdd α) where
  mul_one := add_zero (α := α)
  one_mul := zero_add (α := α)

def IsAddZeroClass.ofAddCommMagma [IsAddCommMagma α₀] (h: ∀x: α₀, 0 + x = x) : IsAddZeroClass α₀ where
  zero_add := h
  add_zero x := by rw [add_comm]; apply h

def IsMulZeroClass.ofCommMagma [Zero α₁] [IsCommMagma α₁] (h: ∀x: α₁, 0 * x = 0) : IsMulZeroClass α₁ where
  zero_mul := h
  mul_zero x := by rw [mul_comm]; apply h

def IsMulOneClass.ofCommMagma [IsCommMagma α₁] (h: ∀x: α₁, 1 * x = x) : IsMulOneClass α₁ where
  one_mul := h
  mul_one x := by rw [mul_comm]; apply h

def all_eq_zero_of_trivial [Zero α₁] [IsMulZeroClass α₁] [IsMulOneClass α₁] (triv: (0: α₁) = (1: α₁)) (a: α₁) : a = 0 := by
  rw [←mul_one a, ←triv, mul_zero]

def nsmulRec : ℕ -> α₀ -> α₀
| 0, _ => 0
| n + 1, a => nsmulRec n a + a

def npowRec : ℕ -> α₁ -> α₁ := nsmulRec (α₀ := AddOfMul α₁)

class IsAddMonoid extends IsAddSemigroup α, IsAddZeroClass α: Prop where
  zero_nsmul (a: α) : 0 • a = 0 := by intros; rfl
  succ_nsmul (n: ℕ) (a: α) : (n + 1) • a = n • a + a := by intros; rfl
class IsMonoid extends IsSemigroup α, IsMulOneClass α: Prop where
  npow_zero (a: α) : a ^ 0 = 1 := by intros; rfl
  npow_succ (n: ℕ) (a: α) : a ^ (n + 1) = a ^ n * a := by intros; rfl

export IsAddMonoid (zero_nsmul succ_nsmul)
export IsMonoid (npow_zero npow_succ)

instance [IsMonoid α] : IsAddMonoid (AddOfMul α) where
  zero_nsmul := npow_zero (α := α)
  succ_nsmul := npow_succ (α := α)
instance [IsAddMonoid α] : IsMonoid (MulOfAdd α) where
  npow_zero := zero_nsmul (α := α)
  npow_succ := succ_nsmul (α := α)

-- def zero_nsmul [IsAddMonoid α₀] (a: α₀) : 0 • a = 0 := IsAddMonoid.nsmul_zero a
-- def succ_nsmul [IsAddMonoid α₀] (n: ℕ) (a: α₀) : (n + 1) • a = n • a + a := IsAddMonoid.nsmul_succ n a
-- def npow_zero [IsMonoid α₁] (a: α₁) : a ^ 0 = 1 := IsMonoid.npow_zero a
-- def npow_succ [IsMonoid α₁] (n: ℕ) (a: α₁) : a ^ (n + 1) = a ^ n * a := IsMonoid.npow_succ n a
def nsmul_zero [IsAddMonoid α₀] (a: ℕ) : a • (0: α₀) = 0 := by
  induction a with
  | zero => rw [zero_nsmul]
  | succ a ih => rw [succ_nsmul, ih, add_zero]
def one_npow [IsMonoid α₁] (a: ℕ) : (1: α₁) ^ a = 1 := nsmul_zero (α₀ := AddOfMul α₁) _

def one_nsmul [IsAddMonoid α₀] (a: α₀) : 1 • a = a := by rw [succ_nsmul, zero_nsmul, zero_add]
def npow_one [IsMonoid α₁] (a: α₁) : a ^ 1 = a := one_nsmul (α₀ := AddOfMul α₁) _

def nsmul_eq_nsmulRec [IsAddMonoid α₀] (n: ℕ) (a: α₀) : n • a = nsmulRec n a := by
  induction n with
  | zero => rw [zero_nsmul]; rfl
  | succ n ih => rw [succ_nsmul, ih]; rfl

def npow_eq_npowRec [IsMonoid α₁] (n: ℕ) (a: α₁) : a ^ n = npowRec n a :=
  nsmul_eq_nsmulRec (α₀ := AddOfMul α₁) _ _

def succ_nsmul' [IsAddMonoid α₀] (n: ℕ) (a: α₀) : (n + 1) • a = a + n • a := by
  have : IsAddSemigroup α₀ := IsAddMonoid.toIsAddSemigroup
  induction n with
  | zero =>
    rw [zero_nsmul, add_zero, succ_nsmul, zero_nsmul, zero_add]
  | succ n ih => rw [succ_nsmul n, ←add_assoc, ←ih, succ_nsmul (n + 1)]
def npow_succ' [IsMonoid α₁] (n: ℕ) (a: α₁) : a ^ (n + 1) = a * a ^ n :=
  succ_nsmul' (α₀ := AddOfMul α₁) _ _

def add_nsmul [IsAddMonoid α₀] (n m: ℕ) (a: α₀) : (n + m) • a = n • a + m • a := by
  have : IsAddSemigroup α₀ := IsAddMonoid.toIsAddSemigroup
  induction m with
  | zero => rw [Nat.add_zero, zero_nsmul, add_zero]
  | succ m ih => rw [Nat.add_succ, succ_nsmul, succ_nsmul, ←add_assoc, ih]
def npow_add [IsMonoid α₁] (n m: ℕ) (a: α₁) : a ^ (n + m) = a ^ n * a ^ m :=
  add_nsmul (α₀ := AddOfMul α₁) _ _ _

def nsmul_add [IsAddMonoid α₀] [IsAddCommMagma α₀] (n: ℕ) (x y: α₀) : n • (x + y) = n • x + n • y := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, zero_nsmul, add_zero]
  | succ n ih =>
    rw [succ_nsmul, ih, add_assoc, add_comm _ (x + y), ←add_assoc, ←add_assoc, ←succ_nsmul, add_assoc, ←succ_nsmul']

def mul_npow [IsMonoid α₁] [IsCommMagma α₁] (n: ℕ) (x y: α₁) : (x * y) ^ n = x ^ n * y ^ n :=
  nsmul_add (α₀ := AddOfMul α₁) _ _ _

def mul_nsmul [IsAddMonoid α₀] (n m: ℕ) (x: α₀) : (m * n) • x = m • n • x := by
  induction m with
  | zero => rw [Nat.zero_mul, zero_nsmul, zero_nsmul]
  | succ m ih => rw [succ_nsmul, Nat.succ_mul, add_nsmul, ih]

def npow_mul [IsMonoid α₁] (n m: ℕ) (x: α₁) : x ^ (m * n) = (x ^ n) ^ m :=
  mul_nsmul (α₀ := AddOfMul α₁) _ _ _

class IsInvolutiveNeg: Prop where
  neg_neg (a: α): - -a = a
class IsInvolutiveInv: Prop where
  inv_inv (a: α): a⁻¹⁻¹ = a

export IsInvolutiveNeg (neg_neg)
export IsInvolutiveInv (inv_inv)

instance [IsInvolutiveInv α] : IsInvolutiveNeg (AddOfMul α) where
  neg_neg := inv_inv (α := α)
instance [IsInvolutiveNeg α] : IsInvolutiveInv (MulOfAdd α) where
  inv_inv := neg_neg (α := α)

def sub' (a b: α₀) : α₀ := a + -b
def div' (a b: α₁) : α₁ := a * b⁻¹

def zsmulRec : ℤ -> α₀ -> α₀
| .ofNat n, a => n • a
| .negSucc n, a => -((n + 1) • a)

def zpowRec : ℤ -> α₁ -> α₁ := zsmulRec (α₀ := AddOfMul α₁)

class IsSubNegMonoid extends IsAddMonoid α: Prop where
  sub_eq_add_neg (a b: α) : a - b = a + -b
  zsmul_ofNat (n: ℕ) (a: α) : (n: ℤ) • a = n • a
  zsmul_negSucc (n: ℕ) (a: α) : (Int.negSucc n) • a = -(n.succ • a)

class IsDivInvMonoid extends IsMonoid α: Prop where
  div_eq_mul_inv (a b: α) : a / b = a * b⁻¹
  zpow_ofNat (n: ℕ) (a: α) : a ^ (n: ℤ) = a ^ n
  zpow_negSucc (n: ℕ) (a: α) : a ^ (Int.negSucc n) = (a ^ n.succ)⁻¹

export IsSubNegMonoid (sub_eq_add_neg zsmul_ofNat zsmul_negSucc)
export IsDivInvMonoid (div_eq_mul_inv zpow_ofNat zpow_negSucc)

instance [IsDivInvMonoid α] : IsSubNegMonoid (AddOfMul α) where
  sub_eq_add_neg := div_eq_mul_inv (α := α)
  zsmul_ofNat := zpow_ofNat (α := α)
  zsmul_negSucc := zpow_negSucc (α := α)
instance [IsSubNegMonoid α] : IsDivInvMonoid (MulOfAdd α) where
  div_eq_mul_inv := sub_eq_add_neg (α := α)
  zpow_ofNat := zsmul_ofNat (α := α)
  zpow_negSucc := zsmul_negSucc (α := α)

instance [IsDivInvMonoid α] : IsSubNegMonoid (AddOfMul α) where
  sub_eq_add_neg := div_eq_mul_inv (α := α)
  zsmul_ofNat := zpow_ofNat (α := α)
  zsmul_negSucc := zpow_negSucc (α := α)
instance [IsSubNegMonoid α] : IsDivInvMonoid (MulOfAdd α) where
  div_eq_mul_inv := sub_eq_add_neg (α := α)
  zpow_ofNat := zsmul_ofNat (α := α)
  zpow_negSucc := zsmul_negSucc (α := α)

def neg_one_zsmul [IsSubNegMonoid α₀] (a: α₀) : (-1) • a = -a := by erw [zsmul_negSucc, one_nsmul]
def zpow_neg_one [IsDivInvMonoid α₁] (a: α₁) : a ^ (-1) = a⁻¹ := neg_one_zsmul (α₀ := AddOfMul α₁) _

class IsNegZeroClass: Prop where
  neg_zero: -(0: α) = 0
class IsInvOneClass: Prop where
  inv_one: (1: α)⁻¹ = 1

export IsNegZeroClass (neg_zero)
export IsInvOneClass (inv_one)

instance [IsInvOneClass α] : IsNegZeroClass (AddOfMul α) where
  neg_zero := inv_one (α := α)
instance [IsNegZeroClass α] : IsInvOneClass (MulOfAdd α) where
  inv_one := neg_zero (α := α)

def zsmul_zero [IsSubNegMonoid α₀] [IsNegZeroClass α₀] (a: ℤ) : a • (0: α₀) = 0 := by
  cases a
  erw [zsmul_ofNat, nsmul_zero]
  rw [zsmul_negSucc, nsmul_zero, neg_zero]

def zero_zsmul [IsSubNegMonoid α₀] (a: α₀) : (0: ℤ) • a = 0 := by
  have : 0 = Int.ofNat 0 := rfl
  erw [this, zsmul_ofNat, zero_nsmul]

def one_zsmul [IsSubNegMonoid α₀] (a: α₀) : (1: ℤ) • a = a := by
  have : 1 = Int.ofNat 1 := rfl
  erw [this, zsmul_ofNat, one_nsmul]

def one_zpow [IsDivInvMonoid α₁] [IsInvOneClass α₁] (a: ℤ) : (1: α₁) ^ a = 1 :=
  zsmul_zero (α₀ := AddOfMul α₁) _

def zpow_zero [IsDivInvMonoid α₁] (a: α₁) : a ^ (0: ℤ) = 1 :=
  zero_zsmul (α₀ := AddOfMul α₁) _

def zpow_one [IsDivInvMonoid α₁] (a: α₁) : a ^ (1: ℤ) = a :=
  one_zsmul (α₀ := AddOfMul α₁) _

def sub_zero [IsSubNegMonoid α₀] [IsNegZeroClass α₀] (a: α₀): a - 0 = a := by
  rw [sub_eq_add_neg, neg_zero, add_zero]

def dov_one [IsDivInvMonoid α₁] [IsInvOneClass α₁] (a: α₁): a / 1 = a :=
  sub_zero (α₀ := AddOfMul α₁) _

class IsSubtractionMonoid extends IsSubNegMonoid α, IsInvolutiveNeg α: Prop where
  neg_add_rev (a b: α) : -(a + b) = -b + -a
  neg_eq_of_add_left {a b: α} : a + b = 0 -> -a = b

class IsDivisionMonoid extends IsDivInvMonoid α, IsInvolutiveInv α: Prop where
  inv_mul_rev (a b: α) : (a * b)⁻¹ = b⁻¹ * a⁻¹
  inv_eq_of_mul_left {a b: α} : a * b = 1 -> a⁻¹ = b

export IsSubtractionMonoid (neg_add_rev neg_eq_of_add_left)
export IsDivisionMonoid (inv_mul_rev inv_eq_of_mul_left)

instance [IsDivisionMonoid α] : IsSubtractionMonoid (AddOfMul α) where
  neg_add_rev := inv_mul_rev (α := α)
  neg_eq_of_add_left := inv_eq_of_mul_left (α := α)
instance [IsSubtractionMonoid α] : IsDivisionMonoid (MulOfAdd α) where
  inv_mul_rev := neg_add_rev (α := α)
  inv_eq_of_mul_left := neg_eq_of_add_left (α := α)

def neg_eq_of_add_right [IsSubtractionMonoid α₀] {a b: α₀} : a + b = 0 -> a = -b := by
  intro h
  rw [←neg_eq_of_add_left h, neg_neg]
def inv_eq_of_mul_right [IsDivisionMonoid α₁] {a b: α₁} : a * b = 1 -> a = b⁻¹ :=
  neg_eq_of_add_right (α₀ := AddOfMul α₁)

class IsAddGroup extends IsSubNegMonoid α: Prop where
  neg_add_cancel (a: α): -a + a = 0
class IsGroup extends IsDivInvMonoid α: Prop where
  inv_mul_cancel (a: α): a⁻¹ * a = 1

export IsAddGroup (neg_add_cancel)
export IsGroup (inv_mul_cancel)

instance [IsGroup α] : IsAddGroup (AddOfMul α) where
  neg_add_cancel := inv_mul_cancel (α := α)
instance [IsAddGroup α] : IsGroup (MulOfAdd α) where
  inv_mul_cancel := neg_add_cancel (α := α)

def left_neg_eq_right_neg [IsAddGroup α₀] { a b c: α₀ } (hba : b + a = 0) (hac : a + c = 0) : b = c := by
  rw [← zero_add c, ← hba, add_assoc, hac, add_zero b]
def left_inv_eq_right_inv [IsGroup α₁] { a b c: α₁ } (hba : b * a = 1) (hac : a * c = 1) : b = c :=
  left_neg_eq_right_neg (α₀ := AddOfMul α₁) hba hac

private theorem neg_eq_of_add [IsAddGroup α₀] { a b: α₀ } (h : a + b = 0) : -a = b :=
  left_neg_eq_right_neg (neg_add_cancel a) h

instance IsAddGroup.toInvolutNeg [IsAddGroup α] : IsInvolutiveNeg α where
  neg_neg a := neg_eq_of_add (neg_add_cancel a)
instance IsGroup.toInvolutInv [IsGroup α] : IsInvolutiveInv α where
  inv_inv := neg_neg (α := AddOfMul α)

def add_neg_cancel [IsAddGroup α₀] (a: α₀): a + -a = 0 := by
  conv => { lhs; lhs; rw [←neg_neg a] }
  rw [neg_add_cancel]
def mul_inv_cancel [IsGroup α₁] (a: α₁): a * a⁻¹ = 1 :=
  add_neg_cancel (α₀ := AddOfMul α₁) _

def sub_self [IsAddGroup α₀] (a: α₀) : a - a = 0 := by
  rw [sub_eq_add_neg, add_neg_cancel]
def div_self [IsGroup α₁] (a: α₁) : a / a = 1 :=
  sub_self (α₀ := AddOfMul α₁) _

instance [IsAddGroup α] : IsSubtractionMonoid α where
  neg_add_rev := by
    intro a b
    apply neg_eq_of_add
    rw [add_assoc, ←add_assoc b, add_neg_cancel, zero_add, add_neg_cancel]
  neg_eq_of_add_left := neg_eq_of_add

instance [IsGroup α] : IsDivisionMonoid α where
  inv_mul_rev := neg_add_rev (α := AddOfMul α)
  inv_eq_of_mul_left := neg_eq_of_add_left (α := AddOfMul α)

instance [IsAddGroup α] : IsAddRightCancel α where
  add_right_cancel := by
    intro a b k h
    have : (a + k) - k = (b + k) - k := by rw [h]
    rw [
      sub_eq_add_neg, sub_eq_add_neg,
      add_assoc, add_assoc, add_neg_cancel, add_zero, add_zero] at this
    assumption

instance [IsGroup α] : IsRightCancel α where
  mul_right_cancel := add_right_cancel (α := AddOfMul α)

instance [IsAddGroup α] : IsAddLeftCancel α where
  add_left_cancel := by
    intro a b k h
    have : -k + (k + a) = -k + (k + b) := by rw [h]
    rw [←add_assoc, ←add_assoc, neg_add_cancel, zero_add, zero_add] at this
    assumption

instance [IsGroup α] : IsLeftCancel α where
  mul_left_cancel := add_left_cancel (α := AddOfMul α)

instance [IsAddGroup α] : IsNegZeroClass α where
  neg_zero := by
    apply neg_eq_of_add
    rw [add_zero]

instance [IsGroup α] : IsInvOneClass α where
  inv_one := neg_zero (α := AddOfMul α)

def neg_sub [IsAddGroup α₀] (a b: α₀) : -(a - b) = b - a := by
  rw [sub_eq_add_neg, neg_add_rev, neg_neg, ←sub_eq_add_neg]

def sub_sub [IsAddGroup α₀] (a b c: α₀) : a - (b - c) = a + c - b := by
  rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, neg_add_rev, neg_neg, add_assoc]

def sub_add_cancel [IsAddGroup α₀] (a b: α₀) : a - b + b = a := by
  rw [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero]

def eq_of_sub_eq_zero [IsAddGroup α₀] {a b: α₀} : a - b = 0 -> a = b := by
  intro h
  rw [sub_eq_add_neg] at h
  have := neg_eq_of_add_right h
  rw [neg_neg] at this
  assumption

def inv_div [IsGroup α₁] (a b: α₁) : (a / b)⁻¹ = b / a :=
  neg_sub (α₀ := AddOfMul α₁) _ _
def div_div [IsGroup α₁] (a b c: α₁) : a / (b / c) = a * c / b :=
  sub_sub (α₀ := AddOfMul α₁) _ _ _

def div_mul_cancel [IsGroup α₁] (a b: α₁) : a / b * b = a :=
  sub_add_cancel (α₀ := AddOfMul α₁) _ _

def eq_of_div_eq_one [IsGroup α₁] {a b: α₁} : a / b = 1 -> a = b :=
  eq_of_sub_eq_zero (α₀ := AddOfMul α₁)

def neg_eq_neg_one_zsmul [IsAddGroup α₀] (a: α₀) : -a = -1 • a := by
  have : -1 = Int.negSucc 0 := rfl
  erw [this, zsmul_negSucc, one_nsmul]

def inv_eq_zpow_neg_one [IsGroup α₁] (a: α₁) : a⁻¹ = a ^ (-1) :=
  neg_eq_neg_one_zsmul (α₀ := AddOfMul α₁) _

class IsLeftDistrib: Prop where
  left_distrib (k a b: α): k * (a + b) = k * a + k * b
class IsRightDistrib: Prop where
  right_distrib (a b k: α): (a + b) * k = a * k + b * k

export IsLeftDistrib (left_distrib)
export IsRightDistrib (right_distrib)

def mul_add [IsLeftDistrib R] (k a b: R): k * (a + b) = k * a + k * b := left_distrib k a b
def add_mul [IsRightDistrib R] (a b k: R): (a + b) * k = a * k + b * k := right_distrib a b k

instance (priority := 100) [IsCommMagma α] [IsLeftDistrib α] : IsRightDistrib α where
  right_distrib a b k := by
    iterate 3 rw [mul_comm _ k]
    rw [mul_add]
instance (priority := 100) [IsCommMagma α] [IsRightDistrib α] : IsLeftDistrib α where
  left_distrib k a b := by
    iterate 3 rw [mul_comm k]
    rw [add_mul]

def natCastRec : ℕ -> α
| 0 => 0
| n + 1 => natCastRec n + 1

def intCastRec : ℤ -> α
| .ofNat n => NatCast.natCast n
| .negSucc n => -NatCast.natCast n.succ

class IsAddMonoidWithOne extends IsAddMonoid α: Prop where
  natCast_zero : NatCast.natCast 0 = (0: α)
  natCast_succ (n: ℕ) : NatCast.natCast n.succ = NatCast.natCast n + (1: α)
  ofNat_zero : OfNat.ofNat (α := α) 0 = 0
  ofNat_one : OfNat.ofNat (α := α) 1 = 1
  ofNat_eq_natCast (n: ℕ): OfNat.ofNat (α := α) (n + 2) = NatCast.natCast (n + 2)

export IsAddMonoidWithOne (natCast_zero natCast_succ ofNat_zero ofNat_one ofNat_eq_natCast)

def natCast_one [IsAddMonoidWithOne R₀] : (NatCast.natCast 1: R₀) = 1 := by
  rw [natCast_succ, natCast_zero, zero_add]

class IsAddGroupWithOne extends IsAddGroup α, IsAddMonoidWithOne α: Prop where
  intCast_ofNat (n: ℕ) : IntCast.intCast n = (NatCast.natCast n: α)
  intCast_negSucc (n: ℕ) : IntCast.intCast (Int.negSucc n) = -(NatCast.natCast n.succ: α)

export IsAddGroupWithOne (intCast_ofNat intCast_negSucc)

class IsSemiring extends
  IsAddCommMagma α, IsAddMonoidWithOne α,
  IsSemigroup α, IsMulZeroClass α, IsMulOneClass α,
  IsLeftDistrib α, IsRightDistrib α, IsMonoid α : Prop where

instance [IsAddCommMagma α] [IsAddMonoidWithOne α] [IsSemigroup α] [IsMulZeroClass α] [IsMulOneClass α] [IsLeftDistrib α] [IsRightDistrib α] [IsMonoid α] : IsSemiring α where
  npow_zero := npow_zero
  npow_succ := npow_succ

class IsRing extends IsSemiring α, IsAddGroupWithOne α : Prop where

instance [IsSemiring α] [IsAddGroupWithOne α] : IsRing α where
  intCast_ofNat := intCast_ofNat
  intCast_negSucc := intCast_negSucc
  sub_eq_add_neg := sub_eq_add_neg
  zsmul_ofNat := zsmul_ofNat
  zsmul_negSucc := zsmul_negSucc
  neg_add_cancel := neg_add_cancel

def mul_sub [IsRing R] (k a b: R): k * (a - b) = k * a - k * b := by
  rw [sub_eq_add_neg, sub_eq_add_neg, mul_add]
  congr 1
  symm
  apply neg_eq_of_add
  rw [←mul_add, add_neg_cancel, mul_zero]

def sub_mul [IsRing R] (k a b: R): (a - b) * k = a * k - b * k := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_mul]
  congr 1
  symm
  apply neg_eq_of_add
  rw [←add_mul, add_neg_cancel, zero_mul]

def neg_mul_left [IsAddGroup R₀] [IsRightDistrib R₀] [IsMulZeroClass R₀] (a b: R₀) : -(a * b) = -a * b := by
  apply neg_eq_of_add
  rw [←add_mul, add_neg_cancel, zero_mul]
def neg_mul_right [IsAddGroup R₀] [IsLeftDistrib R₀] [IsMulZeroClass R₀] (a b: R₀) : -(a * b) = a * -b := by
  apply neg_eq_of_add
  rw [←mul_add, add_neg_cancel, mul_zero]

def nsmul_eq_natCast_mul [IsSemiring R₀] (n: ℕ) (x: R₀) : n • x = n * x := by
  induction n with
  | zero => rw [zero_nsmul, Nat.cast, natCast_zero, zero_mul]
  | succ n ih => rw [succ_nsmul, ih, Nat.cast, natCast_succ, add_mul, one_mul]

def zsmul_eq_intCast_mul [IsRing R₀] (n: ℤ) (x: R₀) : n • x = n * x := by
  cases n with
  | ofNat n =>
    erw [zsmul_ofNat n, Int.cast, intCast_ofNat, nsmul_eq_natCast_mul]
  | negSucc n =>
    rw [zsmul_negSucc, Int.cast, intCast_negSucc, nsmul_eq_natCast_mul, neg_mul_left]

def add_one_mul [IsMulOneClass R₀] [IsRightDistrib R₀] (a b: R₀) : (a + 1) * b = a * b + b := by rw [add_mul, one_mul]
def mul_add_one [IsMulOneClass R₀] [IsLeftDistrib R₀] (a b: R₀) : a * (b + 1) = a * b + a := by rw [mul_add, mul_one]
def one_add_mul [IsMulOneClass R₀] [IsRightDistrib R₀] (a b: R₀) : (1 + a) * b = b + a * b := by rw [add_mul, one_mul]
def mul_one_add [IsMulOneClass R₀] [IsLeftDistrib R₀] (a b: R₀) : a * (1 + b) = a + a * b := by rw [mul_add, mul_one]

def two_mul [IsAddMonoidWithOne R₀] [IsRightDistrib R₀] [IsMulOneClass R₀] (a: R₀) : 2 * a = a + a := by
  rw [ofNat_eq_natCast, Nat.zero_add, natCast_succ, natCast_succ,
    natCast_zero, zero_add, add_mul, one_mul]
def mul_two [IsAddMonoidWithOne R₀] [IsLeftDistrib R₀] [IsMulOneClass R₀] (a: R₀) : a * 2 = a + a := by
  rw [ofNat_eq_natCast, Nat.zero_add, natCast_succ, natCast_succ,
    natCast_zero, zero_add, mul_add, mul_one]

class IsMulAction [IsMonoid R] : Prop where
  one_smul: ∀a: M, (1: R) • a = a
  mul_smul: ∀x y: R, ∀b: M, (x * y) • b = x • y • b

export IsMulAction (one_smul mul_smul)

class IsDistribMulAction [IsMonoid R] [IsAddMonoid M] extends IsMulAction R M : Prop where
  smul_zero: ∀a: R, a • (0: M) = 0
  smul_add: ∀a: R, ∀x y: M, a • (x + y) = a • x + a • y

export IsDistribMulAction (smul_zero smul_add)

class IsModule [IsSemiring R] [IsAddCommMagma M] [IsAddMonoid M] extends IsDistribMulAction R M: Prop where
  add_smul: ∀r s: R, ∀x: M, (r + s) • x = r • x + s • x
  zero_smul: ∀x: M, (0: R) • x = 0

export IsModule (add_smul zero_smul)

class IsNonUnitalNonAssocSemiring extends IsAddCommMagma α, IsAddMonoid α, IsLeftDistrib α, IsRightDistrib α, IsMulZeroClass α: Prop

instance
  [IsAddCommMagma α] [IsAddMonoid α]
  [IsLeftDistrib α] [IsRightDistrib α]
  [IsMulZeroClass α]
  : IsNonUnitalNonAssocSemiring α where

class IsNonAssocSemiring extends IsNonUnitalNonAssocSemiring α, IsMulOneClass α, IsAddMonoidWithOne α: Prop

instance
  [IsNonUnitalNonAssocSemiring α]
  [IsMulOneClass α]
  [IsAddMonoidWithOne α]
  : IsNonAssocSemiring α where
  natCast_zero := natCast_zero
  natCast_succ := natCast_succ
  ofNat_zero := IsAddMonoidWithOne.ofNat_zero
  ofNat_one := IsAddMonoidWithOne.ofNat_one
  ofNat_eq_natCast := IsAddMonoidWithOne.ofNat_eq_natCast

instance [IsSemiring α] : IsNonAssocSemiring α where
  natCast_zero := natCast_zero
  natCast_succ := natCast_succ
  ofNat_zero := IsAddMonoidWithOne.ofNat_zero
  ofNat_one := IsAddMonoidWithOne.ofNat_one
  ofNat_eq_natCast := IsAddMonoidWithOne.ofNat_eq_natCast

def natCast_add [IsSemiring R₀] (a b: ℕ) : (NatCast.natCast (a + b): R₀) = NatCast.natCast a + NatCast.natCast b := by
  induction b with
  | zero => rw [natCast_zero, Nat.add_zero, add_zero]
  | succ b ih => rw [Nat.add_succ, natCast_succ, natCast_succ, ←add_assoc, ih]

def natCast_mul [IsSemiring R₀] (a b: ℕ) : (NatCast.natCast (a * b): R₀) = NatCast.natCast a * NatCast.natCast b := by
  induction b with
  | zero => rw [Nat.mul_zero, natCast_zero, mul_zero]
  | succ b ih => rw [Nat.mul_succ, natCast_add, natCast_succ, mul_add, mul_one, ih]

def intCast_zero [IsRing R₀] : (IntCast.intCast 0: R₀) = 0 := by
  have : 0 = Int.ofNat 0 := rfl
  erw [this, intCast_ofNat, natCast_zero]

def intCast_succ [IsRing R₀] (a: ℤ) : (IntCast.intCast (a + 1): R₀) = IntCast.intCast a + 1 := by
  cases a with
  | ofNat a =>
    have : 1 = Int.ofNat 1 := rfl
    erw [this, intCast_ofNat,
      Int.ofNat_eq_coe,
      ←Int.ofNat_eq_coe, intCast_ofNat, natCast_add, natCast_one]
  | negSucc a =>
    cases a with
    | zero =>
      suffices (IntCast.intCast 0: R₀) = IntCast.intCast (Int.negSucc 0) + 1 from this
      rw [intCast_zero, intCast_negSucc, natCast_one, neg_add_cancel]
    | succ a =>
      suffices (IntCast.intCast (Int.negSucc a): R₀) = IntCast.intCast (Int.negSucc (a + 1)) + 1 from this
      rw [intCast_negSucc, intCast_negSucc, natCast_succ (a + 1),]
      apply neg_eq_of_add
      rw [neg_add_rev, add_assoc, add_comm _ 1, ←add_assoc (-1), neg_add_cancel, zero_add, add_neg_cancel]
def intCast_pred [IsRing R₀] (a: ℤ) : (IntCast.intCast (a - 1): R₀) = IntCast.intCast a - 1 := by
  suffices (IntCast.intCast (a - 1): R₀) = (IntCast.intCast (a - 1) + 1) - 1 by
    rw [←intCast_succ, Int.sub_add_cancel] at this
    exact this
  rw [sub_eq_add_neg _ (1: R₀), add_assoc, add_neg_cancel, add_zero]

def intCast_add [IsRing R₀] (a b: ℤ) : (IntCast.intCast (a + b): R₀) = IntCast.intCast a + IntCast.intCast b := by
  induction b using Int.induction with
  | zero => rw [intCast_zero, Int.add_zero, add_zero]
  | succ b ih => rw [←Int.add_assoc, intCast_succ, intCast_succ, ih, add_assoc]
  | pred b ih => rw [←Int.add_sub_assoc, intCast_pred, intCast_pred, ih, sub_eq_add_neg, add_assoc, sub_eq_add_neg]

def intCast_neg [IsRing R₀] (a: ℤ) : (IntCast.intCast (-a): R₀) = -IntCast.intCast a := by
  symm
  apply neg_eq_of_add
  rw [←intCast_add, Int.add_right_neg, intCast_zero]

def intCast_sub [IsRing R₀] (a b: ℤ) : (IntCast.intCast (a - b): R₀) = IntCast.intCast a - IntCast.intCast b := by
  rw [Int.sub_eq_add_neg, intCast_add, intCast_neg, sub_eq_add_neg]

def intCast_mul [IsRing R₀] (a b: ℤ) : (IntCast.intCast (a * b): R₀) = IntCast.intCast a * IntCast.intCast b := by
  induction b using Int.induction with
  | zero => rw [Int.mul_zero, intCast_zero, mul_zero]
  | succ b ih => rw [Int.mul_add, Int.mul_one, intCast_succ, mul_add, intCast_add, ih, mul_one]
  | pred b ih => rw [Int.mul_sub, Int.mul_one, intCast_pred, mul_sub, intCast_sub, ih, mul_one]

def succ_zsmul [IsAddGroup α₀]  (x: ℤ) (a: α₀) : (x + 1) • a = x • a + a := by
  cases x with
  | ofNat x =>
    have : (1: ℤ) = ↑(1: ℕ) := rfl
    erw [this, Int.ofNat_eq_coe, Int.ofNat_add_ofNat, ←Int.ofNat_eq_coe, ←Int.ofNat_eq_coe, zsmul_ofNat, zsmul_ofNat, succ_nsmul]
  | negSucc x =>
  cases x with
  | zero =>
    have : Int.negSucc 0 = -1 := rfl
    rw [this, Int.add_left_neg, zero_zsmul, ←neg_eq_neg_one_zsmul, neg_add_cancel]
  | succ x =>
    have : (1: ℤ) = ↑(1: ℕ) := rfl
    rw [this, Int.negSucc_add_ofNat, Int.subNatNat_of_lt, Nat.succ_sub_succ, Nat.sub_zero, Nat.add_one, Nat.pred_succ]
    rw [zsmul_negSucc, zsmul_negSucc, succ_nsmul' x.succ, neg_add_rev, add_assoc, neg_add_cancel, add_zero]
    apply Nat.succ_lt_succ
    apply Nat.zero_lt_succ

def pred_zsmul [IsAddGroup α₀]  (x: ℤ) (a: α₀) : (x - 1) • a = x • a - a := by
  conv in x • a => {
    rw [←Int.sub_add_cancel x 1]
  }
  rw [succ_zsmul, sub_eq_add_neg _ a, add_assoc, add_neg_cancel, add_zero]

def add_zsmul [IsAddGroup α₀] (x y: ℤ) (a: α₀) : (x + y) • a = x • a + y • a := by
  induction y using Int.induction with
  | zero => rw [Int.add_zero, zero_zsmul, add_zero]
  | succ y ih => rw [←Int.add_assoc, succ_zsmul, succ_zsmul, ←add_assoc, ih]
  | pred y ih => rw [←Int.add_sub_assoc, pred_zsmul, pred_zsmul, sub_eq_add_neg (y • a) a, ←add_assoc, ih, ←sub_eq_add_neg]

def neg_zsmul [IsAddGroup α₀] (x: ℤ) (a: α₀) : (-x) • a = -(x • a) := by
  symm
  apply neg_eq_of_add
  rw [←add_zsmul, Int.add_right_neg, zero_zsmul]

def zsmul_add [IsAddGroup α₀] [IsAddCommMagma α₀] (x: ℤ) (a b: α₀) : x • (a + b) = x • a + x • b := by
  induction x using Int.induction with
  | zero => rw [zero_zsmul, zero_zsmul, zero_zsmul, add_zero]
  | succ y ih => rw [succ_zsmul, ih, add_comm a b, add_assoc, ←add_assoc (y • b), ←succ_zsmul, add_comm _ a, ←add_assoc, ←succ_zsmul]
  | pred y ih => rw [pred_zsmul, ih, sub_eq_add_neg, neg_add_rev a b, add_assoc, ←add_assoc (y • b), ←sub_eq_add_neg _ b, ←pred_zsmul, add_comm _ (-a), ←add_assoc, ←sub_eq_add_neg, ←pred_zsmul]

def zsmul_neg [IsAddGroup α₀] [IsAddCommMagma α₀] (x: ℤ) (a: α₀) : x • (-a) = -(x • a) := by
  symm
  apply neg_eq_of_add
  rw [←zsmul_add, add_neg_cancel, zsmul_zero]

def zsmul_sub [IsAddGroup α₀] [IsAddCommMagma α₀] (x: ℤ) (a b: α₀) : x • (a - b) = x • a - x • b := by
  rw [sub_eq_add_neg, sub_eq_add_neg, zsmul_add, zsmul_neg]

def sub_zsmul [IsAddGroup α₀] (x y: ℤ) (a: α₀) : (x - y) • a = x • a - y • a := by
  rw [Int.sub_eq_add_neg, sub_eq_add_neg, add_zsmul, neg_zsmul]

def mul_zsmul [IsAddGroup α₀]  [IsAddCommMagma α₀] (x y: ℤ) (a: α₀) : (x * y) • a = x • y • a := by
  induction y using Int.induction with
  | zero => rw [Int.mul_zero, zero_zsmul, zsmul_zero]
  | succ y ih => rw [Int.mul_add, Int.mul_one, add_zsmul, add_zsmul, one_zsmul, zsmul_add, ih]
  | pred y ih => rw [Int.mul_sub, Int.mul_one, sub_zsmul, sub_zsmul, one_zsmul, zsmul_sub, ih]

variable [CheckedInvert α (P := fun x => x ≠ 0)] [CheckedInvert α₀ (P := fun x => x ≠ 0)]
variable [CheckedDiv α (P := fun x => x ≠ 0)] [CheckedDiv α₀ (P := fun x => x ≠ 0)]

class IsNonCommField extends IsRing α : Prop where
  mul_inv?_cancel: ∀(a: α) (h: a ≠ 0), a * a⁻¹? = 1
  div_eq_mul_inv?: ∀(a b: α) (h: b ≠ 0), a /? b = a * b⁻¹?
  zpow_ofNat (n: ℕ) (a: α) : a ^ (n: ℤ) = a ^ n
  zpow_negSucc (n: ℕ) (a: α) (h: a ≠ 0) : a ^ (Int.negSucc n) = (a⁻¹? ^ n.succ)

export IsNonCommField (
  mul_inv?_cancel
  div_eq_mul_inv?
  zpow_ofNat
  zpow_negSucc
)

class IsField extends IsNonCommField α, IsCommMagma α : Prop where
