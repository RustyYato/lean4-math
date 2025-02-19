import Math.Algebra.Monoid.Defs
import Math.Data.StdInt.Basic
import Math.Function.Basic

class IsInvolutiveNeg (α: Type*) [Neg α]: Prop where
  neg_neg (a: α): - -a = a
class IsInvolutiveInv (α: Type*) [Inv α]: Prop where
  inv_inv (a: α): a⁻¹⁻¹ = a

def neg_neg [Neg α] [IsInvolutiveNeg α] (a: α): - -a = a := IsInvolutiveNeg.neg_neg _
def inv_inv [Inv α] [IsInvolutiveInv α] (a: α): a⁻¹⁻¹ = a := IsInvolutiveInv.inv_inv _

instance [Inv α] [IsInvolutiveInv α] : IsInvolutiveNeg (AddOfMul α) where
  neg_neg := inv_inv (α := α)
instance [Neg α] [IsInvolutiveNeg α] : IsInvolutiveInv (MulOfAdd α) where
  inv_inv := neg_neg (α := α)
instance [Neg α] [IsInvolutiveNeg α] : IsInvolutiveNeg αᵐᵒᵖ :=
  inferInstanceAs (IsInvolutiveNeg α)
instance [Inv α] [IsInvolutiveInv α] : IsInvolutiveInv αᵐᵒᵖ where
  inv_inv := inv_inv (α := α)

def neg_inj [Neg α] [IsInvolutiveNeg α] {a b: α} : -a = -b ↔ a = b :=
  Function.Injective.eq_iff <| by
    intro a b eq
    rw [←neg_neg a, ←neg_neg b, eq]

def inv_inj [Inv α] [IsInvolutiveInv α] {a b: α} : a⁻¹ = b⁻¹ ↔ a = b :=
  neg_inj (α := AddOfMul α)

def sub' [Add α] [Neg α] (a b: α) := a + -b
def div' [Mul α] [Inv α] (a b: α) := a * b⁻¹

def zsmulRec [AddMonoidOps α] [Neg α] : ℤ -> α -> α
| .ofNat n, a => n • a
| .negSucc n, a => -((n + 1) • a)

def zpowRec [MonoidOps α] [Inv α] : ℤ -> α -> α := zsmulRec (α := AddOfMul α)

def instSub [Add α] [Neg α] : Sub α := ⟨sub'⟩
def instDiv [Mul α] [Inv α] : Div α := ⟨div'⟩

def instZSMul [AddMonoidOps α] [Neg α] : SMul ℤ α := ⟨zsmulRec⟩
def instZPow [MonoidOps α] [Inv α] : Pow α ℤ := ⟨flip zpowRec⟩

class AddGroupOps (α: Type*) extends AddMonoidOps α, Neg α, Sub α where
  zsmul: ℤ -> α -> α := by exact SMul.smul
class GroupOps (α: Type*) extends MonoidOps α, Inv α, Div α where
  div := div'
  zpow: α -> ℤ -> α := by exact Pow.pow

instance [AddMonoidOps α] [Neg α] [Sub α] [SMul ℤ α] : AddGroupOps α where
instance [MonoidOps α] [Inv α] [Div α] [Pow α ℤ] : GroupOps α where

instance (priority := 50) [AddGroupOps α] : SMul ℤ α where
  smul := AddGroupOps.zsmul
instance (priority := 50) [GroupOps α] : Pow α ℤ where
  pow := GroupOps.zpow

variable [AddGroupOps α] [GroupOps α]

section DivInvMonoid

class IsSubNegMonoid (α: Type*) [AddGroupOps α] extends IsAddMonoid α: Prop where
  sub_eq_add_neg (a b: α) : a - b = a + -b
  zsmul_ofNat (n: ℕ) (a: α) : (n: ℤ) • a = n • a
  zsmul_negSucc (n: ℕ) (a: α) : (Int.negSucc n) • a = -(n.succ • a)

class IsDivInvMonoid (α: Type*) [GroupOps α] extends IsMonoid α: Prop where
  div_eq_mul_inv (a b: α) : a / b = a * b⁻¹
  zpow_ofNat (n: ℕ) (a: α) : a ^ (n: ℤ) = a ^ n
  zpow_negSucc (n: ℕ) (a: α) : a ^ (Int.negSucc n) = (a ^ n.succ)⁻¹

variable [IsSubNegMonoid α] [IsDivInvMonoid α]

def sub_eq_add_neg (a b: α) : a - b = a + -b := IsSubNegMonoid.sub_eq_add_neg _ _
def zsmul_ofNat (n: ℕ) (a: α) : (n: ℤ) • a = n • a := IsSubNegMonoid.zsmul_ofNat _ _
def zsmul_negSucc (n: ℕ) (a: α) : (Int.negSucc n) • a = -(n.succ • a) := IsSubNegMonoid.zsmul_negSucc _ _
def div_eq_mul_inv (a b: α) : a / b = a * b⁻¹ := IsDivInvMonoid.div_eq_mul_inv _ _
def zpow_ofNat (n: ℕ) (a: α) : a ^ (n: ℤ) = a ^ n := IsDivInvMonoid.zpow_ofNat _ _
def zpow_negSucc (n: ℕ) (a: α) : a ^ (Int.negSucc n) = (a ^ n.succ)⁻¹ := IsDivInvMonoid.zpow_negSucc _ _

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

instance [IsSubNegMonoid α] : IsSubNegMonoid αᵐᵒᵖ :=
  inferInstanceAs (IsSubNegMonoid α)
instance [IsDivInvMonoid α] : IsDivInvMonoid αᵐᵒᵖ where
  div_eq_mul_inv _ _ := rfl
  zpow_ofNat := zpow_ofNat (α := α)
  zpow_negSucc := zpow_negSucc (α := α)

def neg_one_zsmul [IsSubNegMonoid α] (a: α) : (-1) • a = -a := by erw [zsmul_negSucc, one_nsmul]
def zpow_neg_one [IsDivInvMonoid α] (a: α) : a ^ (-1) = a⁻¹ := neg_one_zsmul (α := AddOfMul α) _

class IsNegZeroClass (α: Type*) [Zero α] [Neg α]: Prop where
  neg_zero: -(0: α) = 0
class IsInvOneClass (α: Type*) [One α] [Inv α]: Prop where
  inv_one: (1: α)⁻¹ = 1

def neg_zero [Neg α] [Zero α] [IsNegZeroClass α]: -(0: α) = 0 := IsNegZeroClass.neg_zero
def inv_one [Inv α] [One α] [IsInvOneClass α]: (1: α)⁻¹ = 1 := IsInvOneClass.inv_one

instance [One α] [Inv α] [IsInvOneClass α] : IsNegZeroClass (AddOfMul α) where
  neg_zero := inv_one (α := α)
instance [Zero α] [Neg α] [IsNegZeroClass α] : IsInvOneClass (MulOfAdd α) where
  inv_one := neg_zero (α := α)
instance [Zero α] [Neg α] [IsNegZeroClass α] : IsNegZeroClass αᵐᵒᵖ :=
  inferInstanceAs (IsNegZeroClass α)
instance [One α] [Inv α] [IsInvOneClass α] : IsInvOneClass αᵐᵒᵖ :=
  inferInstanceAs (IsInvOneClass α)

def zsmul_zero [IsSubNegMonoid α] [IsNegZeroClass α] (a: ℤ) : a • (0: α) = 0 := by
  cases a
  erw [zsmul_ofNat, nsmul_zero]
  rw [zsmul_negSucc, nsmul_zero, neg_zero]

def zero_zsmul [IsSubNegMonoid α] (a: α) : (0: ℤ) • a = 0 := by
  have : 0 = Int.ofNat 0 := rfl
  erw [this, zsmul_ofNat, zero_nsmul]

def one_zsmul [IsSubNegMonoid α] (a: α) : (1: ℤ) • a = a := by
  have : 1 = Int.ofNat 1 := rfl
  erw [this, zsmul_ofNat, one_nsmul]

def one_zpow [IsDivInvMonoid α] [IsInvOneClass α] (a: ℤ) : (1: α) ^ a = 1 :=
  zsmul_zero (α := AddOfMul α) _

def zpow_zero [IsDivInvMonoid α] (a: α) : a ^ (0: ℤ) = 1 :=
  zero_zsmul (α := AddOfMul α) _

def zpow_one [IsDivInvMonoid α] (a: α) : a ^ (1: ℤ) = a :=
  one_zsmul (α := AddOfMul α) _

def sub_zero [IsSubNegMonoid α] [IsNegZeroClass α] (a: α): a - 0 = a := by
  rw [sub_eq_add_neg, neg_zero, add_zero]

def div_one [IsDivInvMonoid α] [IsInvOneClass α] (a: α): a / 1 = a :=
  sub_zero (α := AddOfMul α) _

end DivInvMonoid

section DivisionMonoid

class IsSubtractionMonoid (α: Type*) [AddGroupOps α] extends IsSubNegMonoid α, IsInvolutiveNeg α: Prop where
  neg_add_rev (a b: α) : -(a + b) = -b + -a
  neg_eq_of_add_left {a b: α} : a + b = 0 -> -a = b

class IsDivisionMonoid (α: Type*) [GroupOps α] extends IsDivInvMonoid α, IsInvolutiveInv α: Prop where
  inv_mul_rev (a b: α) : (a * b)⁻¹ = b⁻¹ * a⁻¹
  inv_eq_of_mul_left {a b: α} : a * b = 1 -> a⁻¹ = b

variable [IsSubtractionMonoid α] [IsDivisionMonoid α]

def neg_add_rev (a b: α) : -(a + b) = -b + -a := IsSubtractionMonoid.neg_add_rev _ _
def neg_eq_of_add_left {a b: α} : a + b = 0 -> -a = b := IsSubtractionMonoid.neg_eq_of_add_left

def inv_mul_rev (a b: α) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := IsDivisionMonoid.inv_mul_rev _ _
def inv_eq_of_mul_left {a b: α} : a * b = 1 -> a⁻¹ = b := IsDivisionMonoid.inv_eq_of_mul_left

instance [IsDivisionMonoid α] : IsSubtractionMonoid (AddOfMul α) where
  neg_add_rev := inv_mul_rev (α := α)
  neg_eq_of_add_left := inv_eq_of_mul_left (α := α)
instance [IsSubtractionMonoid α] : IsDivisionMonoid (MulOfAdd α) where
  inv_mul_rev := neg_add_rev (α := α)
  inv_eq_of_mul_left := neg_eq_of_add_left (α := α)
instance [IsSubtractionMonoid α] : IsSubtractionMonoid αᵐᵒᵖ :=
  inferInstanceAs (IsSubtractionMonoid α)

def neg_eq_of_add_right [IsSubtractionMonoid α] {a b: α} : a + b = 0 -> a = -b := by
  intro h
  rw [←neg_eq_of_add_left h, neg_neg]
def inv_eq_of_mul_right [IsDivisionMonoid α] {a b: α} : a * b = 1 -> a = b⁻¹ :=
  neg_eq_of_add_right (α := AddOfMul α)

def neg_sub_neg [IsAddCommMagma α] [IsSubtractionMonoid α] (a b: α) : -a - -b = b - a := by
  rw [sub_eq_add_neg, neg_neg, add_comm, sub_eq_add_neg]

end DivisionMonoid

section Group

class IsAddGroup (α: Type*) [AddGroupOps α] extends IsSubNegMonoid α: Prop where
  neg_add_cancel (a: α): -a + a = 0
class IsGroup (α: Type*) [GroupOps α] extends IsDivInvMonoid α: Prop where
  inv_mul_cancel (a: α): a⁻¹ * a = 1

variable [IsAddGroup α] [IsGroup α]

def neg_add_cancel (a: α): -a + a = 0 := IsAddGroup.neg_add_cancel _
def inv_mul_cancel (a: α): a⁻¹ * a = 1 := IsGroup.inv_mul_cancel _

instance [IsGroup α] : IsAddGroup (AddOfMul α) where
  neg_add_cancel := inv_mul_cancel (α := α)
instance [IsAddGroup α] : IsGroup (MulOfAdd α) where
  inv_mul_cancel := neg_add_cancel (α := α)
instance [IsAddGroup α] : IsAddGroup αᵐᵒᵖ :=
  inferInstanceAs (IsAddGroup α)

def left_neg_eq_right_neg [IsAddGroup α] { a b c: α } (hba : b + a = 0) (hac : a + c = 0) : b = c := by
  rw [← zero_add c, ← hba, add_assoc, hac, add_zero b]
def left_inv_eq_right_inv [IsGroup α] { a b c: α } (hba : b * a = 1) (hac : a * c = 1) : b = c :=
  left_neg_eq_right_neg (α := AddOfMul α) hba hac

private def neg_eq_of_add [IsAddGroup α] { a b: α } (h : a + b = 0) : -a = b :=
  left_neg_eq_right_neg (neg_add_cancel a) h

instance IsAddGroup.toInvolutNeg [IsAddGroup α] : IsInvolutiveNeg α where
  neg_neg a := neg_eq_of_add (neg_add_cancel a)
instance IsGroup.toInvolutInv [IsGroup α] : IsInvolutiveInv α where
  inv_inv := neg_neg (α := AddOfMul α)

def add_neg_cancel [IsAddGroup α] (a: α): a + -a = 0 := by
  conv => { lhs; lhs; rw [←neg_neg a] }
  rw [neg_add_cancel]
def mul_inv_cancel [IsGroup α] (a: α): a * a⁻¹ = 1 :=
  add_neg_cancel (α := AddOfMul α) _

def sub_self [IsAddGroup α] (a: α) : a - a = 0 := by
  rw [sub_eq_add_neg, add_neg_cancel]
def div_self [IsGroup α] (a: α) : a / a = 1 :=
  sub_self (α := AddOfMul α) _

instance [IsGroup α] : IsGroup αᵐᵒᵖ where
  inv_mul_cancel := mul_inv_cancel (α := α)

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

def eq_one_of_mul_left_id [IsGroup α]  (a: α) (h: ∀x: α, a * x = x) : a = 1 := by
  apply mul_right_cancel
  rw [h 1]
  rw [one_mul]

def eq_one_of_mul_right_id [IsGroup α]  (a: α) (h: ∀x: α, x * a = x) : a = 1 :=
  eq_one_of_mul_left_id (α := αᵐᵒᵖ) a h

def neg_sub [IsAddGroup α] (a b: α) : -(a - b) = b - a := by
  rw [sub_eq_add_neg, neg_add_rev, neg_neg, ←sub_eq_add_neg]

def sub_sub [IsAddGroup α] (a b c: α) : a - (b - c) = a + c - b := by
  rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, neg_add_rev, neg_neg, add_assoc]

def sub_add_cancel [IsAddGroup α] (a b: α) : a - b + b = a := by
  rw [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero]

def add_sub_cancel [IsAddGroup α] [IsAddCommMagma α] (a b: α) : a + (b - a) = b := by
  rw [sub_eq_add_neg, add_left_comm, add_neg_cancel, add_zero]

def sub_add (k a b: α) : k - (a + b) = k - b - a := by
  rw [sub_eq_add_neg, neg_add_rev, ←add_assoc, sub_eq_add_neg, sub_eq_add_neg]

def eq_of_sub_eq_zero [IsAddGroup α] {a b: α} : a - b = 0 -> a = b := by
  intro h
  rw [sub_eq_add_neg] at h
  have := neg_eq_of_add_right h
  rw [neg_neg] at this
  assumption

def inv_div [IsGroup α] (a b: α) : (a / b)⁻¹ = b / a :=
  neg_sub (α := AddOfMul α) _ _
def div_div [IsGroup α] (a b c: α) : a / (b / c) = a * c / b :=
  sub_sub (α := AddOfMul α) _ _ _

def div_mul_cancel [IsGroup α] (a b: α) : a / b * b = a :=
  sub_add_cancel (α := AddOfMul α) _ _

def eq_of_div_eq_one [IsGroup α] {a b: α} : a / b = 1 -> a = b :=
  eq_of_sub_eq_zero (α := AddOfMul α)

def neg_eq_neg_one_zsmul [IsAddGroup α] (a: α) : -a = -1 • a := by
  have : -1 = Int.negSucc 0 := rfl
  erw [this, zsmul_negSucc, one_nsmul]

def inv_eq_zpow_neg_one [IsGroup α] (a: α) : a⁻¹ = a ^ (-1) :=
  neg_eq_neg_one_zsmul (α := AddOfMul α) _

def succ_zsmul [IsAddGroup α] (x: ℤ) (a: α) : (x + 1) • a = x • a + a := by
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

def pred_zsmul [IsAddGroup α] (x: ℤ) (a: α) : (x - 1) • a = x • a - a := by
  conv in x • a => {
    rw [←Int.sub_add_cancel x 1]
  }
  rw [succ_zsmul, sub_eq_add_neg _ a, add_assoc, add_neg_cancel, add_zero]

def add_zsmul [IsAddGroup α] (x y: ℤ) (a: α) : (x + y) • a = x • a + y • a := by
  induction y using Int.induction with
  | zero => rw [Int.add_zero, zero_zsmul, add_zero]
  | succ y ih => rw [←Int.add_assoc, succ_zsmul, succ_zsmul, ←add_assoc, ih]
  | pred y ih => rw [←Int.add_sub_assoc, pred_zsmul, pred_zsmul, sub_eq_add_neg (y • a) a, ←add_assoc, ih, ←sub_eq_add_neg]

def neg_zsmul [IsAddGroup α] (x: ℤ) (a: α) : (-x) • a = -(x • a) := by
  symm
  apply neg_eq_of_add
  rw [←add_zsmul, Int.add_right_neg, zero_zsmul]

def zsmul_add [IsAddGroup α] [IsAddCommMagma α] (x: ℤ) (a b: α) : x • (a + b) = x • a + x • b := by
  induction x using Int.induction with
  | zero => rw [zero_zsmul, zero_zsmul, zero_zsmul, add_zero]
  | succ y ih => rw [succ_zsmul, ih, add_comm a b, add_assoc, ←add_assoc (y • b), ←succ_zsmul, add_comm _ a, ←add_assoc, ←succ_zsmul]
  | pred y ih => rw [pred_zsmul, ih, sub_eq_add_neg, neg_add_rev a b, add_assoc, ←add_assoc (y • b), ←sub_eq_add_neg _ b, ←pred_zsmul, add_comm _ (-a), ←add_assoc, ←sub_eq_add_neg, ←pred_zsmul]

def zsmul_neg [IsAddGroup α] [IsAddCommMagma α] (x: ℤ) (a: α) : x • (-a) = -(x • a) := by
  symm
  apply neg_eq_of_add
  rw [←zsmul_add, add_neg_cancel, zsmul_zero]

def zsmul_sub [IsAddGroup α] [IsAddCommMagma α] (x: ℤ) (a b: α) : x • (a - b) = x • a - x • b := by
  rw [sub_eq_add_neg, sub_eq_add_neg, zsmul_add, zsmul_neg]

def sub_zsmul [IsAddGroup α] (x y: ℤ) (a: α) : (x - y) • a = x • a - y • a := by
  rw [Int.sub_eq_add_neg, sub_eq_add_neg, add_zsmul, neg_zsmul]

def mul_zsmul [IsAddGroup α] [IsAddCommMagma α] (x y: ℤ) (a: α) : (x * y) • a = x • y • a := by
  induction y using Int.induction with
  | zero => rw [Int.mul_zero, zero_zsmul, zsmul_zero]
  | succ y ih => rw [Int.mul_add, Int.mul_one, add_zsmul, add_zsmul, one_zsmul, zsmul_add, ih]
  | pred y ih => rw [Int.mul_sub, Int.mul_one, sub_zsmul, sub_zsmul, one_zsmul, zsmul_sub, ih]

def zpow_succ [IsGroup α] (x: ℤ) (a: α) : a ^ (x + 1) = a ^ x * a :=
  succ_zsmul (α := AddOfMul α) _ _

def zpow_pred [IsGroup α] (x: ℤ) (a: α) : a ^ (x - 1) = a ^ x / a :=
  pred_zsmul (α := AddOfMul α) _ _

def zpow_add [IsGroup α] (x y: ℤ) (a: α) : a ^ (x + y) = a ^ x * a ^ y :=
  add_zsmul (α := AddOfMul α) _ _ _

def zpow_neg [IsGroup α] (x: ℤ) (a: α) : a ^ (-x) = (a ^ x)⁻¹ :=
  neg_zsmul (α := AddOfMul α) _ _

def mul_zpow [IsGroup α] [IsCommMagma α] (x: ℤ) (a b: α) : (a * b) ^ x = a ^ x * b ^ x :=
  zsmul_add (α := AddOfMul α) _ _ _

def inv_zpow [IsGroup α] [IsCommMagma α] (x: ℤ) (a: α) : (a⁻¹) ^ x = (a ^ x)⁻¹ :=
  zsmul_neg (α := AddOfMul α) _ _

def div_zpow [IsGroup α] [IsCommMagma α] (x: ℤ) (a b: α) : (a / b) ^ x = a ^ x / b ^ x :=
  zsmul_sub (α := AddOfMul α) _ _ _

def zpow_sub [IsGroup α] (x y: ℤ) (a: α) : a ^ (x - y) = a ^ x / a ^ y :=
  sub_zsmul (α := AddOfMul α) _ _ _

def zpow_mul [IsGroup α]  [IsCommMagma α] (x y: ℤ) (a: α) : a ^ (x * y) = (a ^ y) ^ x :=
  mul_zsmul (α := AddOfMul α) _ _ _

end Group
