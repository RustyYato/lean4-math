import Math.Type.Notation
import Math.Data.StdInt.Basic
import Math.AxiomBlame
import Math.Ops.Checked
import Math.Algebra.Notation
import Math.Algebra.AddMul
import Math.Relation.Basic

class IsNontrivial (α: Type*) [Zero α] [One α]: Prop where
  zero_ne_one: 0 ≠ (1: α)

export IsNontrivial (zero_ne_one)

class IsAddSemigroup (α: Type*) [Add α]: Prop where
  add_assoc (a b c: α) : a + b + c = a + (b + c)
class IsSemigroup (α: Type*) [Mul α]: Prop where
  mul_assoc (a b c: α) : a * b * c = a * (b * c)

export IsAddSemigroup (add_assoc)
export IsSemigroup (mul_assoc)

instance [Mul α] [IsSemigroup α] : IsAddSemigroup (AddOfMul α) where
  add_assoc := mul_assoc (α := α)
instance [Add α] [IsAddSemigroup α] : IsSemigroup (MulOfAdd α) where
  mul_assoc := add_assoc (α := α)

class IsAddCommMagma (α: Type*) [Add α]: Prop where
  add_comm (a b: α) : a + b = b + a
class IsCommMagma (α: Type*) [Mul α]: Prop where
  mul_comm (a b: α) : a * b = b * a

export IsAddCommMagma (add_comm)
export IsCommMagma (mul_comm)

instance [Mul α] [IsCommMagma α] : IsAddCommMagma (AddOfMul α) where
  add_comm := mul_comm (α := α)
instance [Add α] [IsAddCommMagma α] : IsCommMagma (MulOfAdd α) where
  mul_comm := add_comm (α := α)

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

export IsAddLeftCancel (add_left_cancel)
export IsAddRightCancel (add_right_cancel)
export IsLeftCancel (mul_left_cancel)
export IsRightCancel (mul_right_cancel)

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

export IsAddZeroClass (zero_add add_zero)
export IsMulZeroClass (zero_mul mul_zero)
export IsMulOneClass (one_mul mul_one)

instance [Mul α] [One α] [IsMulOneClass α] : IsAddZeroClass (AddOfMul α) where
  add_zero := mul_one (α := α)
  zero_add := one_mul (α := α)
instance [Add α] [Zero α] [IsAddZeroClass α] : IsMulOneClass (MulOfAdd α) where
  mul_one := add_zero (α := α)
  one_mul := zero_add (α := α)

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

def nsmulRec [Zero α] [Add α] : ℕ -> α -> α
| 0, _ => 0
| n + 1, a => nsmulRec n a + a

def npowRec [One α] [Mul α] : ℕ -> α -> α := nsmulRec (α := AddOfMul α)

class AddMonoidOps (α: Type*) extends Add α, Zero α where
  nsmul: ℕ -> α -> α := by exact SMul.smul
class MonoidOps (α: Type*) extends Mul α, One α where
  npow: α -> ℕ -> α := by exact Pow.pow

instance (priority := 50) [Add α] [Zero α] [SMul ℕ α] : AddMonoidOps α where
instance (priority := 50) [Mul α] [One α] [Pow α ℕ] : MonoidOps α where

instance (priority := 50) [AddMonoidOps α] : SMul ℕ α where
  smul := AddMonoidOps.nsmul
instance (priority := 50) [MonoidOps α] : Pow α ℕ where
  pow := MonoidOps.npow

class IsAddMonoid (α: Type*) [AddMonoidOps α] extends IsAddSemigroup α, IsAddZeroClass α: Prop where
  zero_nsmul (a: α) : 0 • a = 0 := by intros; rfl
  succ_nsmul (n: ℕ) (a: α) : (n + 1) • a = n • a + a := by intros; rfl
class IsMonoid (α: Type*) [MonoidOps α] extends IsSemigroup α, IsMulOneClass α: Prop where
  npow_zero (a: α) : a ^ 0 = 1 := by intros; rfl
  npow_succ (n: ℕ) (a: α) : a ^ (n + 1) = a ^ n * a := by intros; rfl

export IsAddMonoid (zero_nsmul succ_nsmul)
export IsMonoid (npow_zero npow_succ)

instance [MonoidOps α] [IsMonoid α] : IsAddMonoid (AddOfMul α) where
  zero_nsmul := npow_zero (α := α)
  succ_nsmul := npow_succ (α := α)
instance [AddMonoidOps α] [IsAddMonoid α] : IsMonoid (MulOfAdd α) where
  npow_zero := zero_nsmul (α := α)
  npow_succ := succ_nsmul (α := α)

def nsmul_zero [AddMonoidOps α] [IsAddMonoid α] (a: ℕ) : a • (0: α) = 0 := by
  induction a with
  | zero => rw [zero_nsmul]
  | succ a ih => rw [succ_nsmul, ih, add_zero]
def one_npow [MonoidOps α] [IsMonoid α] (a: ℕ) : (1: α) ^ a = 1 := nsmul_zero (α := AddOfMul α) _

def one_nsmul [AddMonoidOps α] [IsAddMonoid α] (a: α) : 1 • a = a := by rw [succ_nsmul, zero_nsmul, zero_add]
def npow_one [MonoidOps α] [IsMonoid α] (a: α) : a ^ 1 = a := one_nsmul (α := AddOfMul α) _

def nsmul_eq_nsmulRec [AddMonoidOps α] [IsAddMonoid α] (n: ℕ) (a: α) : n • a = nsmulRec n a := by
  induction n with
  | zero => rw [zero_nsmul]; rfl
  | succ n ih => rw [succ_nsmul, ih]; rfl

def npow_eq_npowRec [MonoidOps α] [IsMonoid α] (n: ℕ) (a: α) : a ^ n = npowRec n a :=
  nsmul_eq_nsmulRec (α := AddOfMul α) _ _

def succ_nsmul' [AddMonoidOps α] [IsAddMonoid α] (n: ℕ) (a: α) : (n + 1) • a = a + n • a := by
  have : IsAddSemigroup α := IsAddMonoid.toIsAddSemigroup
  induction n with
  | zero =>
    rw [zero_nsmul, add_zero, succ_nsmul, zero_nsmul, zero_add]
  | succ n ih => rw [succ_nsmul n, ←add_assoc, ←ih, succ_nsmul (n + 1)]
def npow_succ' [MonoidOps α] [IsMonoid α] (n: ℕ) (a: α) : a ^ (n + 1) = a * a ^ n :=
  succ_nsmul' (α := AddOfMul α) _ _

def add_nsmul [AddMonoidOps α] [IsAddMonoid α] (n m: ℕ) (a: α) : (n + m) • a = n • a + m • a := by
  induction m with
  | zero => rw [Nat.add_zero, zero_nsmul, add_zero]
  | succ m ih => rw [Nat.add_succ, succ_nsmul, succ_nsmul, ←add_assoc, ih]
def npow_add [MonoidOps α] [IsMonoid α] (n m: ℕ) (a: α) : a ^ (n + m) = a ^ n * a ^ m :=
  add_nsmul (α := AddOfMul α) _ _ _

def nsmul_add [AddMonoidOps α] [IsAddMonoid α] [IsAddCommMagma α] (n: ℕ) (x y: α) : n • (x + y) = n • x + n • y := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, zero_nsmul, add_zero]
  | succ n ih =>
    rw [succ_nsmul, ih, add_assoc, add_comm _ (x + y), ←add_assoc, ←add_assoc, ←succ_nsmul, add_assoc, ←succ_nsmul']

def mul_npow [MonoidOps α] [IsMonoid α] [IsCommMagma α] (n: ℕ) (x y: α) : (x * y) ^ n = x ^ n * y ^ n :=
  nsmul_add (α := AddOfMul α) _ _ _

def mul_nsmul [AddMonoidOps α] [IsAddMonoid α] (n m: ℕ) (x: α) : (m * n) • x = m • n • x := by
  induction m with
  | zero => rw [Nat.zero_mul, zero_nsmul, zero_nsmul]
  | succ m ih => rw [succ_nsmul, Nat.succ_mul, add_nsmul, ih]

def npow_mul [MonoidOps α] [IsMonoid α] (n m: ℕ) (x: α) : x ^ (m * n) = (x ^ n) ^ m :=
  mul_nsmul (α := AddOfMul α) _ _ _

section Char

open Classical
variable (α: Type*) [AddMonoidOps α] [IsAddMonoid α]

private
def HasChar (n: Nat) : Prop := ∀(m: Nat), (∀(a: α), m • a = 0) ↔ n ∣ m

private
def existsChar : ∃n, HasChar α n := by
  by_cases h:∃n: Nat, n ≠ 0 ∧ ∀a: α, n • a = 0
  · replace h := Relation.exists_min (· < ·) h
    obtain ⟨n, ⟨npos, h⟩, min_spec⟩ := h
    exists n
    intro m
    apply Iff.intro
    · intro g
      induction m using Nat.strongRecOn with
      | ind m ih =>
      cases m with
      | zero => apply Nat.dvd_zero
      | succ m =>
      have : n ≤ m + 1 := by
        apply Nat.le_of_not_lt
        intro lt
        refine min_spec (m+1) lt ⟨?_, ?_⟩
        intro; contradiction
        assumption
      have := Nat.div_add_mod (m+1) n
      rw [←this] at g; clear this
      conv at g => { intro a; rw [add_nsmul, mul_nsmul, h, zero_add] }
      have := ih ((m+1) % n) ?_ g
      rw [←Nat.div_add_mod (m + 1) n]
      apply Nat.dvd_add
      apply Nat.dvd_mul_right
      assumption
      apply Nat.lt_of_lt_of_le
      apply Nat.mod_lt
      apply Nat.pos_of_ne_zero
      assumption
      assumption
    · intro ⟨k, dvd⟩ a
      rw [dvd, mul_nsmul, h]
  · exists 0
    intro m
    apply Iff.intro
    · intro g
      cases m
      apply Nat.dvd_refl
      rename_i m
      have := h ⟨m+1, Ne.symm (Nat.zero_ne_add_one m), g⟩
      contradiction
    · intro g
      cases Nat.eq_zero_of_zero_dvd g
      intro
      rw [zero_nsmul]

-- the characteristic of a Addition Monoid over α
-- i.e. the smallest non-zero natural such that
-- the product with any element of α is zero
-- or if no such non-zero natural exists, then zero
noncomputable def char : ℕ := Classical.choose (existsChar α)

def char_dvd : ∀(m: Nat), (∀(a: α), m • a = 0) -> char α ∣ m := fun m => (Classical.choose_spec (existsChar α) m).mp
def char_spec : ∀(a: α), char α • a = 0 := (Classical.choose_spec (existsChar α) _).mpr (Nat.dvd_refl _)
def char_eq_of (n: Nat) : (∀a: α, n • a = 0) -> (∀(m: Nat), (∀(a: α), m • a = 0) -> n ∣ m) -> char α = n := by
  intro h g
  apply Nat.dvd_antisymm
  apply char_dvd
  assumption
  apply g
  apply char_spec

end Char

class IsInvolutiveNeg (α: Type*) [Neg α]: Prop where
  neg_neg (a: α): - -a = a
class IsInvolutiveInv (α: Type*) [Inv α]: Prop where
  inv_inv (a: α): a⁻¹⁻¹ = a

export IsInvolutiveNeg (neg_neg)
export IsInvolutiveInv (inv_inv)

instance [Inv α] [IsInvolutiveInv α] : IsInvolutiveNeg (AddOfMul α) where
  neg_neg := inv_inv (α := α)
instance [Neg α] [IsInvolutiveNeg α] : IsInvolutiveInv (MulOfAdd α) where
  inv_inv := neg_neg (α := α)

def sub' [Add α] [Neg α] (a b: α) := a + -b
def div' [Mul α] [Inv α] (a b: α) := a * b⁻¹

def zsmulRec [AddMonoidOps α] [Neg α] : ℤ -> α -> α
| .ofNat n, a => n • a
| .negSucc n, a => -((n + 1) • a)

def zpowRec [MonoidOps α] [Inv α] : ℤ -> α -> α := zsmulRec (α := AddOfMul α)

class AddGroupOps (α: Type*) extends AddMonoidOps α, Neg α, Sub α where
  zsmul: ℤ -> α -> α := by exact SMul.smul
class GroupOps (α: Type*) extends MonoidOps α, Inv α, Div α where
  zpow: α -> ℤ -> α := by exact Pow.pow

instance [AddMonoidOps α] [Neg α] [Sub α] [SMul ℤ α] : AddGroupOps α where
instance [MonoidOps α] [Inv α] [Div α] [Pow α ℤ] : GroupOps α where

instance [AddGroupOps α] : SMul ℤ α where
  smul := AddGroupOps.zsmul
instance [GroupOps α] : Pow α ℤ where
  pow := GroupOps.zpow

class IsSubNegMonoid (α: Type*) [AddGroupOps α] extends IsAddMonoid α: Prop where
  sub_eq_add_neg (a b: α) : a - b = a + -b
  zsmul_ofNat (n: ℕ) (a: α) : (n: ℤ) • a = n • a
  zsmul_negSucc (n: ℕ) (a: α) : (Int.negSucc n) • a = -(n.succ • a)

class IsDivInvMonoid (α: Type*) [GroupOps α] extends IsMonoid α: Prop where
  div_eq_mul_inv (a b: α) : a / b = a * b⁻¹
  zpow_ofNat (n: ℕ) (a: α) : a ^ (n: ℤ) = a ^ n
  zpow_negSucc (n: ℕ) (a: α) : a ^ (Int.negSucc n) = (a ^ n.succ)⁻¹

export IsSubNegMonoid (sub_eq_add_neg zsmul_ofNat zsmul_negSucc)
export IsDivInvMonoid (div_eq_mul_inv zpow_ofNat zpow_negSucc)

instance [GroupOps α] [IsDivInvMonoid α] : IsSubNegMonoid (AddOfMul α) where
  sub_eq_add_neg := div_eq_mul_inv (α := α)
  zsmul_ofNat := zpow_ofNat (α := α)
  zsmul_negSucc := zpow_negSucc (α := α)
instance [AddGroupOps α] [IsSubNegMonoid α] : IsDivInvMonoid (MulOfAdd α) where
  div_eq_mul_inv := sub_eq_add_neg (α := α)
  zpow_ofNat := zsmul_ofNat (α := α)
  zpow_negSucc := zsmul_negSucc (α := α)

instance [GroupOps α] [IsDivInvMonoid α] : IsSubNegMonoid (AddOfMul α) where
  sub_eq_add_neg := div_eq_mul_inv (α := α)
  zsmul_ofNat := zpow_ofNat (α := α)
  zsmul_negSucc := zpow_negSucc (α := α)
instance [AddGroupOps α] [IsSubNegMonoid α] : IsDivInvMonoid (MulOfAdd α) where
  div_eq_mul_inv := sub_eq_add_neg (α := α)
  zpow_ofNat := zsmul_ofNat (α := α)
  zpow_negSucc := zsmul_negSucc (α := α)

def neg_one_zsmul [AddGroupOps α] [IsSubNegMonoid α] (a: α) : (-1) • a = -a := by erw [zsmul_negSucc, one_nsmul]
def zpow_neg_one [GroupOps α] [IsDivInvMonoid α] (a: α) : a ^ (-1) = a⁻¹ := neg_one_zsmul (α := AddOfMul α) _

class IsNegZeroClass (α: Type*) [Zero α] [Neg α]: Prop where
  neg_zero: -(0: α) = 0
class IsInvOneClass (α: Type*) [One α] [Inv α]: Prop where
  inv_one: (1: α)⁻¹ = 1

export IsNegZeroClass (neg_zero)
export IsInvOneClass (inv_one)

instance [One α] [Inv α] [IsInvOneClass α] : IsNegZeroClass (AddOfMul α) where
  neg_zero := inv_one (α := α)
instance [Zero α] [Neg α] [IsNegZeroClass α] : IsInvOneClass (MulOfAdd α) where
  inv_one := neg_zero (α := α)

def zsmul_zero [AddGroupOps α] [IsSubNegMonoid α] [IsNegZeroClass α] (a: ℤ) : a • (0: α) = 0 := by
  cases a
  erw [zsmul_ofNat, nsmul_zero]
  rw [zsmul_negSucc, nsmul_zero, neg_zero]

def zero_zsmul [AddGroupOps α] [IsSubNegMonoid α] (a: α) : (0: ℤ) • a = 0 := by
  have : 0 = Int.ofNat 0 := rfl
  erw [this, zsmul_ofNat, zero_nsmul]

def one_zsmul [AddGroupOps α] [IsSubNegMonoid α] (a: α) : (1: ℤ) • a = a := by
  have : 1 = Int.ofNat 1 := rfl
  erw [this, zsmul_ofNat, one_nsmul]

def one_zpow [GroupOps α] [IsDivInvMonoid α] [IsInvOneClass α] (a: ℤ) : (1: α) ^ a = 1 :=
  zsmul_zero (α := AddOfMul α) _

def zpow_zero [GroupOps α] [IsDivInvMonoid α] (a: α) : a ^ (0: ℤ) = 1 :=
  zero_zsmul (α := AddOfMul α) _

def zpow_one [GroupOps α] [IsDivInvMonoid α] (a: α) : a ^ (1: ℤ) = a :=
  one_zsmul (α := AddOfMul α) _

def sub_zero [AddGroupOps α] [IsSubNegMonoid α] [IsNegZeroClass α] (a: α): a - 0 = a := by
  rw [sub_eq_add_neg, neg_zero, add_zero]

def dov_one [GroupOps α] [IsDivInvMonoid α] [IsInvOneClass α] (a: α): a / 1 = a :=
  sub_zero (α := AddOfMul α) _

class IsSubtractionMonoid (α: Type*) [AddGroupOps α] extends IsSubNegMonoid α, IsInvolutiveNeg α: Prop where
  neg_add_rev (a b: α) : -(a + b) = -b + -a
  neg_eq_of_add_left {a b: α} : a + b = 0 -> -a = b

class IsDivisionMonoid (α: Type*) [GroupOps α] extends IsDivInvMonoid α, IsInvolutiveInv α: Prop where
  inv_mul_rev (a b: α) : (a * b)⁻¹ = b⁻¹ * a⁻¹
  inv_eq_of_mul_left {a b: α} : a * b = 1 -> a⁻¹ = b

export IsSubtractionMonoid (neg_add_rev neg_eq_of_add_left)
export IsDivisionMonoid (inv_mul_rev inv_eq_of_mul_left)

instance [GroupOps α] [IsDivisionMonoid α] : IsSubtractionMonoid (AddOfMul α) where
  neg_add_rev := inv_mul_rev (α := α)
  neg_eq_of_add_left := inv_eq_of_mul_left (α := α)
instance [AddGroupOps α] [IsSubtractionMonoid α] : IsDivisionMonoid (MulOfAdd α) where
  inv_mul_rev := neg_add_rev (α := α)
  inv_eq_of_mul_left := neg_eq_of_add_left (α := α)

def neg_eq_of_add_right [AddGroupOps α] [IsSubtractionMonoid α] {a b: α} : a + b = 0 -> a = -b := by
  intro h
  rw [←neg_eq_of_add_left h, neg_neg]
def inv_eq_of_mul_right [GroupOps α] [IsDivisionMonoid α] {a b: α} : a * b = 1 -> a = b⁻¹ :=
  neg_eq_of_add_right (α := AddOfMul α)

class IsAddGroup (α: Type*) [AddGroupOps α] extends IsSubNegMonoid α: Prop where
  neg_add_cancel (a: α): -a + a = 0
class IsGroup (α: Type*) [GroupOps α] extends IsDivInvMonoid α: Prop where
  inv_mul_cancel (a: α): a⁻¹ * a = 1

export IsAddGroup (neg_add_cancel)
export IsGroup (inv_mul_cancel)

instance [GroupOps α] [IsGroup α] : IsAddGroup (AddOfMul α) where
  neg_add_cancel := inv_mul_cancel (α := α)
instance [AddGroupOps α] [IsAddGroup α] : IsGroup (MulOfAdd α) where
  inv_mul_cancel := neg_add_cancel (α := α)

def left_neg_eq_right_neg [AddGroupOps α] [IsAddGroup α] { a b c: α } (hba : b + a = 0) (hac : a + c = 0) : b = c := by
  rw [← zero_add c, ← hba, add_assoc, hac, add_zero b]
def left_inv_eq_right_inv [GroupOps α] [IsGroup α] { a b c: α } (hba : b * a = 1) (hac : a * c = 1) : b = c :=
  left_neg_eq_right_neg (α := AddOfMul α) hba hac

private theorem neg_eq_of_add [AddGroupOps α] [IsAddGroup α] { a b: α } (h : a + b = 0) : -a = b :=
  left_neg_eq_right_neg (neg_add_cancel a) h

instance IsAddGroup.toInvolutNeg [AddGroupOps α] [IsAddGroup α] : IsInvolutiveNeg α where
  neg_neg a := neg_eq_of_add (neg_add_cancel a)
instance IsGroup.toInvolutInv [GroupOps α] [IsGroup α] : IsInvolutiveInv α where
  inv_inv := neg_neg (α := AddOfMul α)

def add_neg_cancel [AddGroupOps α] [IsAddGroup α] (a: α): a + -a = 0 := by
  conv => { lhs; lhs; rw [←neg_neg a] }
  rw [neg_add_cancel]
def mul_inv_cancel [GroupOps α] [IsGroup α] (a: α): a * a⁻¹ = 1 :=
  add_neg_cancel (α := AddOfMul α) _

def sub_self [AddGroupOps α] [IsAddGroup α] (a: α) : a - a = 0 := by
  rw [sub_eq_add_neg, add_neg_cancel]
def div_self [GroupOps α] [IsGroup α] (a: α) : a / a = 1 :=
  sub_self (α := AddOfMul α) _

instance [AddGroupOps α] [IsAddGroup α] : IsSubtractionMonoid α where
  neg_add_rev := by
    intro a b
    apply neg_eq_of_add
    rw [add_assoc, ←add_assoc b, add_neg_cancel, zero_add, add_neg_cancel]
  neg_eq_of_add_left := neg_eq_of_add

instance [GroupOps α] [IsGroup α] : IsDivisionMonoid α where
  inv_mul_rev := neg_add_rev (α := AddOfMul α)
  inv_eq_of_mul_left := neg_eq_of_add_left (α := AddOfMul α)

instance [AddGroupOps α] [IsAddGroup α] : IsAddRightCancel α where
  add_right_cancel := by
    intro a b k h
    have : (a + k) - k = (b + k) - k := by rw [h]
    rw [
      sub_eq_add_neg, sub_eq_add_neg,
      add_assoc, add_assoc, add_neg_cancel, add_zero, add_zero] at this
    assumption

instance [GroupOps α] [IsGroup α] : IsRightCancel α where
  mul_right_cancel := add_right_cancel (α := AddOfMul α)

instance [AddGroupOps α] [IsAddGroup α] : IsAddLeftCancel α where
  add_left_cancel := by
    intro a b k h
    have : -k + (k + a) = -k + (k + b) := by rw [h]
    rw [←add_assoc, ←add_assoc, neg_add_cancel, zero_add, zero_add] at this
    assumption

instance [GroupOps α] [IsGroup α] : IsLeftCancel α where
  mul_left_cancel := add_left_cancel (α := AddOfMul α)

instance [AddGroupOps α] [IsAddGroup α] : IsNegZeroClass α where
  neg_zero := by
    apply neg_eq_of_add
    rw [add_zero]

instance [GroupOps α] [IsGroup α] : IsInvOneClass α where
  inv_one := neg_zero (α := AddOfMul α)

def neg_sub [AddGroupOps α] [IsAddGroup α] (a b: α) : -(a - b) = b - a := by
  rw [sub_eq_add_neg, neg_add_rev, neg_neg, ←sub_eq_add_neg]

def sub_sub [AddGroupOps α] [IsAddGroup α] (a b c: α) : a - (b - c) = a + c - b := by
  rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, neg_add_rev, neg_neg, add_assoc]

def sub_add_cancel [AddGroupOps α] [IsAddGroup α] (a b: α) : a - b + b = a := by
  rw [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero]

def eq_of_sub_eq_zero [AddGroupOps α] [IsAddGroup α] {a b: α} : a - b = 0 -> a = b := by
  intro h
  rw [sub_eq_add_neg] at h
  have := neg_eq_of_add_right h
  rw [neg_neg] at this
  assumption

def inv_div [GroupOps α] [IsGroup α] (a b: α) : (a / b)⁻¹ = b / a :=
  neg_sub (α := AddOfMul α) _ _
def div_div [GroupOps α] [IsGroup α] (a b c: α) : a / (b / c) = a * c / b :=
  sub_sub (α := AddOfMul α) _ _ _

def div_mul_cancel [GroupOps α] [IsGroup α] (a b: α) : a / b * b = a :=
  sub_add_cancel (α := AddOfMul α) _ _

def eq_of_div_eq_one [GroupOps α] [IsGroup α] {a b: α} : a / b = 1 -> a = b :=
  eq_of_sub_eq_zero (α := AddOfMul α)

def neg_eq_neg_one_zsmul [AddGroupOps α] [IsAddGroup α] (a: α) : -a = -1 • a := by
  have : -1 = Int.negSucc 0 := rfl
  erw [this, zsmul_negSucc, one_nsmul]

def inv_eq_zpow_neg_one [GroupOps α] [IsGroup α] (a: α) : a⁻¹ = a ^ (-1) :=
  neg_eq_neg_one_zsmul (α := AddOfMul α) _

def succ_zsmul [AddGroupOps α] [IsAddGroup α] (x: ℤ) (a: α) : (x + 1) • a = x • a + a := by
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

def pred_zsmul [AddGroupOps α] [IsAddGroup α] (x: ℤ) (a: α) : (x - 1) • a = x • a - a := by
  conv in x • a => {
    rw [←Int.sub_add_cancel x 1]
  }
  rw [succ_zsmul, sub_eq_add_neg _ a, add_assoc, add_neg_cancel, add_zero]

def add_zsmul [AddGroupOps α] [IsAddGroup α] (x y: ℤ) (a: α) : (x + y) • a = x • a + y • a := by
  induction y using Int.induction with
  | zero => rw [Int.add_zero, zero_zsmul, add_zero]
  | succ y ih => rw [←Int.add_assoc, succ_zsmul, succ_zsmul, ←add_assoc, ih]
  | pred y ih => rw [←Int.add_sub_assoc, pred_zsmul, pred_zsmul, sub_eq_add_neg (y • a) a, ←add_assoc, ih, ←sub_eq_add_neg]

def neg_zsmul [AddGroupOps α] [IsAddGroup α] (x: ℤ) (a: α) : (-x) • a = -(x • a) := by
  symm
  apply neg_eq_of_add
  rw [←add_zsmul, Int.add_right_neg, zero_zsmul]

def zsmul_add [AddGroupOps α] [IsAddGroup α] [IsAddCommMagma α] (x: ℤ) (a b: α) : x • (a + b) = x • a + x • b := by
  induction x using Int.induction with
  | zero => rw [zero_zsmul, zero_zsmul, zero_zsmul, add_zero]
  | succ y ih => rw [succ_zsmul, ih, add_comm a b, add_assoc, ←add_assoc (y • b), ←succ_zsmul, add_comm _ a, ←add_assoc, ←succ_zsmul]
  | pred y ih => rw [pred_zsmul, ih, sub_eq_add_neg, neg_add_rev a b, add_assoc, ←add_assoc (y • b), ←sub_eq_add_neg _ b, ←pred_zsmul, add_comm _ (-a), ←add_assoc, ←sub_eq_add_neg, ←pred_zsmul]

def zsmul_neg [AddGroupOps α] [IsAddGroup α] [IsAddCommMagma α] (x: ℤ) (a: α) : x • (-a) = -(x • a) := by
  symm
  apply neg_eq_of_add
  rw [←zsmul_add, add_neg_cancel, zsmul_zero]

def zsmul_sub [AddGroupOps α] [IsAddGroup α] [IsAddCommMagma α] (x: ℤ) (a b: α) : x • (a - b) = x • a - x • b := by
  rw [sub_eq_add_neg, sub_eq_add_neg, zsmul_add, zsmul_neg]

def sub_zsmul [AddGroupOps α] [IsAddGroup α] (x y: ℤ) (a: α) : (x - y) • a = x • a - y • a := by
  rw [Int.sub_eq_add_neg, sub_eq_add_neg, add_zsmul, neg_zsmul]

def mul_zsmul [AddGroupOps α] [IsAddGroup α] [IsAddCommMagma α] (x y: ℤ) (a: α) : (x * y) • a = x • y • a := by
  induction y using Int.induction with
  | zero => rw [Int.mul_zero, zero_zsmul, zsmul_zero]
  | succ y ih => rw [Int.mul_add, Int.mul_one, add_zsmul, add_zsmul, one_zsmul, zsmul_add, ih]
  | pred y ih => rw [Int.mul_sub, Int.mul_one, sub_zsmul, sub_zsmul, one_zsmul, zsmul_sub, ih]

def succ_zpow [GroupOps α] [IsGroup α] (x: ℤ) (a: α) : a ^ (x + 1) = a ^ x * a :=
  succ_zsmul (α := AddOfMul α) _ _

def pred_zpow [GroupOps α] [IsGroup α] (x: ℤ) (a: α) : a ^ (x - 1) = a ^ x / a :=
  pred_zsmul (α := AddOfMul α) _ _

def add_zpow [GroupOps α] [IsGroup α] (x y: ℤ) (a: α) : a ^ (x + y) = a ^ x * a ^ y :=
  add_zsmul (α := AddOfMul α) _ _ _

def neg_zpow [GroupOps α] [IsGroup α] (x: ℤ) (a: α) : a ^ (-x) = (a ^ x)⁻¹ :=
  neg_zsmul (α := AddOfMul α) _ _

def zpow_add [GroupOps α] [IsGroup α] [IsCommMagma α] (x: ℤ) (a b: α) : (a * b) ^ x = a ^ x * b ^ x :=
  zsmul_add (α := AddOfMul α) _ _ _

def zpow_inv [GroupOps α] [IsGroup α] [IsCommMagma α] (x: ℤ) (a: α) : (a⁻¹) ^ x = (a ^ x)⁻¹ :=
  zsmul_neg (α := AddOfMul α) _ _

def zpow_div [GroupOps α] [IsGroup α] [IsCommMagma α] (x: ℤ) (a b: α) : (a / b) ^ x = a ^ x / b ^ x :=
  zsmul_sub (α := AddOfMul α) _ _ _

def sub_zpow [GroupOps α] [IsGroup α] (x y: ℤ) (a: α) : a ^ (x - y) = a ^ x / a ^ y :=
  sub_zsmul (α := AddOfMul α) _ _ _

def mul_zpow [GroupOps α] [IsGroup α]  [IsCommMagma α] (x y: ℤ) (a: α) : a ^ (x * y) = (a ^ y) ^ x :=
  mul_zsmul (α := AddOfMul α) _ _ _

class IsLeftDistrib (α: Type*) [Add α] [Mul α]: Prop where
  left_distrib (k a b: α): k * (a + b) = k * a + k * b
class IsRightDistrib (α: Type*) [Add α] [Mul α]: Prop where
  right_distrib (a b k: α): (a + b) * k = a * k + b * k

export IsLeftDistrib (left_distrib)
export IsRightDistrib (right_distrib)

def mul_add [Add α] [Mul α] [IsLeftDistrib α] (k a b: α): k * (a + b) = k * a + k * b := left_distrib k a b
def add_mul [Add α] [Mul α] [IsRightDistrib α] (a b k: α): (a + b) * k = a * k + b * k := right_distrib a b k

instance (priority := 100) [Add α] [Mul α] [IsCommMagma α] [IsLeftDistrib α] : IsRightDistrib α where
  right_distrib a b k := by
    iterate 3 rw [mul_comm _ k]
    rw [mul_add]
instance (priority := 100) [Add α] [Mul α] [IsCommMagma α] [IsRightDistrib α] : IsLeftDistrib α where
  left_distrib k a b := by
    iterate 3 rw [mul_comm k]
    rw [add_mul]

def natCastRec [Add α] [Zero α] [One α] : ℕ -> α
| 0 => 0
| n + 1 => natCastRec n + 1

def intCastRec [NatCast α] [Neg α] : ℤ -> α
| .ofNat n => NatCast.natCast n
| .negSucc n => -NatCast.natCast n.succ

class AddMonoidWithOneOps (α: Type*) extends AddMonoidOps α, One α, NatCast α where
  ofNat n : OfNat α (n + 2) := by infer_instance

instance [AddMonoidOps α] [One α] [NatCast α] [∀n, OfNat α (n + 2)] : AddMonoidWithOneOps α where

instance [AddMonoidWithOneOps α] : OfNat α (n + 2) := AddMonoidWithOneOps.ofNat n

class IsAddMonoidWithOne (α: Type*) [AddMonoidWithOneOps α] extends IsAddMonoid α: Prop where
  natCast_zero : ((0: Nat): α) = (0: α)
  natCast_succ (n: ℕ) : (n.succ: α) = (n: α) + (1: α)
  ofNat_eq_natCast (n: ℕ): OfNat.ofNat (α := α) (n + 2) = ((n + 2: Nat): α)

export IsAddMonoidWithOne (natCast_zero natCast_succ ofNat_eq_natCast)

def natCast_eq_nsmul_one [AddMonoidWithOneOps α] [IsAddMonoidWithOne α] (n: Nat) : (n: α) = n • 1  := by
  induction n with
  | zero => rw [zero_nsmul, natCast_zero]
  | succ n ih => rw [natCast_succ, ih, succ_nsmul]

def natCast_one [AddMonoidWithOneOps α] [IsAddMonoidWithOne α] : ((1: Nat): α) = 1 := by
  rw [natCast_succ, natCast_zero, zero_add]

def natCast_add [AddMonoidWithOneOps α] [IsAddMonoidWithOne α] (a b: ℕ) : ((a + b: Nat): α) = a + b := by
  simp [natCast_eq_nsmul_one, add_nsmul]

class AddGroupWithOneOps (α: Type*) extends AddGroupOps α, AddMonoidWithOneOps α, IntCast α where

instance [AddMonoidWithOneOps α] [Neg α] [Sub α] [IntCast α] [SMul ℤ α] : AddGroupWithOneOps α where

class IsAddGroupWithOne (α: Type*) [AddGroupWithOneOps α] extends IsAddGroup α, IsAddMonoidWithOne α: Prop where
  intCast_ofNat (n: ℕ) : ((n: Int): α) = (n: α)
  intCast_negSucc (n: ℕ) : (Int.negSucc n) = -(n.succ: α)

export IsAddGroupWithOne (intCast_ofNat intCast_negSucc)

def intCast_eq_zsmul_one [AddGroupWithOneOps α] [IsAddGroupWithOne α] (n: Int) : (n: α) = n • 1  := by
  cases n with
  | ofNat n => rw [Int.ofNat_eq_coe, intCast_ofNat, natCast_eq_nsmul_one, zsmul_ofNat]
  | negSucc n => rw [intCast_negSucc, zsmul_negSucc, natCast_eq_nsmul_one]

def intCast_zero [AddGroupWithOneOps α] [IsAddGroupWithOne α] : ((0: Int): α) = 0 := by
  have : 0 = Int.ofNat 0 := rfl
  erw [this, intCast_ofNat, natCast_zero]

def intCast_one [AddGroupWithOneOps α] [IsAddGroupWithOne α] : ((1: Int): α) = 1 := by
  have : 1 = Int.ofNat 1 := rfl
  erw [this, intCast_ofNat, natCast_one]

def intCast_succ [AddGroupWithOneOps α] [IsAddGroupWithOne α] (a: ℤ) : ((a + 1: Int): α) = a + 1 := by
  rw [intCast_eq_zsmul_one, intCast_eq_zsmul_one, add_zsmul, one_zsmul]

def intCast_pred [AddGroupWithOneOps α] [IsAddGroupWithOne α] (a: ℤ) : ((a - 1: Int): α) = a - 1 := by
  rw [intCast_eq_zsmul_one, intCast_eq_zsmul_one, sub_zsmul, one_zsmul]

def intCast_add [AddGroupWithOneOps α] [IsAddGroupWithOne α] (a b: ℤ) : ((a + b: Int): α) = a + b := by
  simp only [intCast_eq_zsmul_one, add_zsmul]

def intCast_neg [AddGroupWithOneOps α] [IsAddGroupWithOne α] (a: ℤ) : ((-a: Int): α) = -a := by
  symm
  apply neg_eq_of_add
  rw [←intCast_add, Int.add_right_neg, intCast_zero]

def intCast_sub [AddGroupWithOneOps α] [IsAddGroupWithOne α] (a b: ℤ) : ((a - b: Int): α) = a - b := by
  rw [Int.sub_eq_add_neg, intCast_add, intCast_neg, sub_eq_add_neg]

class SemiringOps (α: Type*) extends AddMonoidWithOneOps α, MonoidOps α where
instance [AddMonoidWithOneOps α] [MonoidOps α] : SemiringOps α where

class IsSemiring (α: Type*) [SemiringOps α] extends
  IsAddCommMagma α, IsAddMonoidWithOne α,
  IsSemigroup α, IsMulZeroClass α, IsMulOneClass α,
  IsLeftDistrib α, IsRightDistrib α, IsMonoid α : Prop where

instance [SemiringOps α] [IsAddCommMagma α] [IsAddMonoidWithOne α] [IsSemigroup α] [IsMulZeroClass α] [IsMulOneClass α] [IsLeftDistrib α] [IsRightDistrib α] [IsMonoid α] : IsSemiring α where
  npow_zero := npow_zero
  npow_succ := npow_succ

def natCast_mul_eq_nsmul [SemiringOps α] [IsSemiring α] (x: α) (r: Nat) : r * x = r • x := by
  induction r with
  | zero => rw [natCast_zero, zero_mul, zero_nsmul]
  | succ r ih => rw [natCast_succ, add_mul, one_mul, succ_nsmul, ih]

def mul_natCast_eq_nsmul [SemiringOps α] [IsSemiring α] (x: α) (r: Nat) : x * r = r • x := by
  induction r with
  | zero => rw [natCast_zero, mul_zero, zero_nsmul]
  | succ r ih => rw [natCast_succ, mul_add, mul_one, succ_nsmul, ih]

def natCast_mul [SemiringOps α] [IsSemiring α] (a b: ℕ) : ((a * b: Nat): α) = a * b := by
  rw [natCast_mul_eq_nsmul, natCast_eq_nsmul_one, mul_nsmul, natCast_eq_nsmul_one]

def char_eq_of_natCast_eq_zero [SemiringOps α] [IsSemiring α] (n: Nat) :
  n = (0: α) -> (∀m: Nat, m = (0: α) -> n ∣ m) -> char α = n := by
  intro h g
  apply char_eq_of
  intro x
  rw [←natCast_mul_eq_nsmul, h, zero_mul]
  intro m g'
  apply g
  rw [natCast_eq_nsmul_one]
  apply g'

class RingOps (α: Type*) extends SemiringOps α, AddGroupWithOneOps α where
instance [SemiringOps α] [Neg α] [Sub α] [IntCast α] [SMul ℤ α] : RingOps α where

class IsRing (α: Type*) [RingOps α] extends IsSemiring α, IsAddGroupWithOne α : Prop where

-- a shortcut instance to prevent timeouts
instance (priority := 5000) [RingOps α] [IsRing α] : IsSemiring α where
  npow_zero := npow_zero
  npow_succ := npow_succ

instance [RingOps α] [IsSemiring α] [IsAddGroupWithOne α] : IsRing α where
  intCast_ofNat := intCast_ofNat
  intCast_negSucc := intCast_negSucc
  sub_eq_add_neg := sub_eq_add_neg
  zsmul_ofNat := zsmul_ofNat
  zsmul_negSucc := zsmul_negSucc
  neg_add_cancel := neg_add_cancel

def mul_sub [RingOps α] [IsRing α] (k a b: α): k * (a - b) = k * a - k * b := by
  rw [sub_eq_add_neg, sub_eq_add_neg, mul_add]
  congr 1
  symm
  apply neg_eq_of_add
  rw [←mul_add, add_neg_cancel, mul_zero]

def sub_mul [RingOps α] [IsRing α] (k a b: α): (a - b) * k = a * k - b * k := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_mul]
  congr 1
  symm
  apply neg_eq_of_add
  rw [←add_mul, add_neg_cancel, zero_mul]

def neg_mul_left [AddGroupOps α] [Mul α] [IsAddGroup α] [IsRightDistrib α] [IsMulZeroClass α] (a b: α) : -(a * b) = -a * b := by
  apply neg_eq_of_add
  rw [←add_mul, add_neg_cancel, zero_mul]
def neg_mul_right [AddGroupOps α] [Mul α] [IsAddGroup α] [IsLeftDistrib α] [IsMulZeroClass α] (a b: α) : -(a * b) = a * -b := by
  apply neg_eq_of_add
  rw [←mul_add, add_neg_cancel, mul_zero]

def nsmul_eq_natCast_mul [SemiringOps α] [IsSemiring α] (n: ℕ) (x: α) : n • x = n * x := by
  induction n with
  | zero => rw [zero_nsmul, natCast_zero, zero_mul]
  | succ n ih => rw [succ_nsmul, ih, natCast_succ, add_mul, one_mul]

def zsmul_eq_intCast_mul [RingOps α] [IsRing α] (n: ℤ) (x: α) : n • x = n * x := by
  cases n with
  | ofNat n =>
    erw [zsmul_ofNat n, intCast_ofNat, nsmul_eq_natCast_mul]
  | negSucc n =>
    rw [zsmul_negSucc, intCast_negSucc, nsmul_eq_natCast_mul, neg_mul_left]

def intCast_mul_eq_zsmul [RingOps α] [IsRing α] (x: α) (r: Int) : r * x = r • x := by
  induction r with
  | ofNat r => erw [intCast_ofNat, zsmul_ofNat, natCast_mul_eq_nsmul]
  | negSucc r => rw [intCast_negSucc, zsmul_negSucc, ←neg_mul_left, natCast_mul_eq_nsmul]

def mul_intCast_eq_zsmul [RingOps α] [IsRing α] (x: α) (r: Int) : x * r = r • x := by
  induction r with
  | ofNat r => erw [intCast_ofNat, zsmul_ofNat, mul_natCast_eq_nsmul]
  | negSucc r => rw [intCast_negSucc, zsmul_negSucc, ←neg_mul_right, mul_natCast_eq_nsmul]

def intCast_mul [RingOps α] [IsRing α] (a b: ℤ) : ((a * b: Int): α) = (a: α) * (b: α) := by
  rw [intCast_mul_eq_zsmul, intCast_eq_zsmul_one, mul_zsmul, intCast_eq_zsmul_one]

def add_one_mul [Mul α] [Add α] [One α] [IsMulOneClass α] [IsRightDistrib α] (a b: α) : (a + 1) * b = a * b + b := by rw [add_mul, one_mul]
def mul_add_one [Mul α] [Add α] [One α] [IsMulOneClass α] [IsLeftDistrib α] (a b: α) : a * (b + 1) = a * b + a := by rw [mul_add, mul_one]
def one_add_mul [Mul α] [Add α] [One α] [IsMulOneClass α] [IsRightDistrib α] (a b: α) : (1 + a) * b = b + a * b := by rw [add_mul, one_mul]
def mul_one_add [Mul α] [Add α] [One α] [IsMulOneClass α] [IsLeftDistrib α] (a b: α) : a * (1 + b) = a + a * b := by rw [mul_add, mul_one]

def two_mul [AddMonoidWithOneOps α] [Mul α] [IsAddMonoidWithOne α] [IsRightDistrib α] [IsMulOneClass α] (a: α) : 2 * a = a + a := by
  rw [ofNat_eq_natCast, Nat.zero_add, natCast_succ, natCast_succ,
    natCast_zero, zero_add, add_mul, one_mul]
def mul_two [AddMonoidWithOneOps α] [Mul α] [IsAddMonoidWithOne α] [IsLeftDistrib α] [IsMulOneClass α] (a: α) : a * 2 = a + a := by
  rw [ofNat_eq_natCast, Nat.zero_add, natCast_succ, natCast_succ,
    natCast_zero, zero_add, mul_add, mul_one]

class IsMulAction (R M: Type*) [MonoidOps R] [SMul R M] [IsMonoid R] : Prop where
  one_smul: ∀a: M, (1: R) • a = a
  mul_smul: ∀x y: R, ∀b: M, (x * y) • b = x • y • b

export IsMulAction (one_smul mul_smul)

class IsDistribMulAction (R M: Type*) [MonoidOps R] [AddMonoidOps M] [SMul R M] [IsMonoid R] [IsAddMonoid M] extends IsMulAction R M : Prop where
  smul_zero: ∀a: R, a • (0: M) = 0
  smul_add: ∀a: R, ∀x y: M, a • (x + y) = a • x + a • y

export IsDistribMulAction (smul_zero smul_add)

class IsModule (R M: Type*) [SemiringOps R] [AddMonoidOps M] [SMul R M] [IsSemiring R] [IsAddCommMagma M] [IsAddMonoid M] extends IsDistribMulAction R M: Prop where
  add_smul: ∀r s: R, ∀x: M, (r + s) • x = r • x + s • x
  zero_smul: ∀x: M, (0: R) • x = 0

export IsModule (add_smul zero_smul)

class IsSMulComm (R S A: Type*) [SMul R A] [SMul S A]: Prop where
  smul_comm: ∀(r: R) (s: S) (x: A), r • s • x = s • r • x

export IsSMulComm (smul_comm)

class IsNonUnitalNonAssocSemiring (α: Type*) [AddMonoidOps α] [Mul α] extends IsAddCommMagma α, IsAddMonoid α, IsLeftDistrib α, IsRightDistrib α, IsMulZeroClass α: Prop

instance
  [AddMonoidOps α] [Mul α]
  [IsAddCommMagma α] [IsAddMonoid α]
  [IsLeftDistrib α] [IsRightDistrib α]
  [IsMulZeroClass α]
  : IsNonUnitalNonAssocSemiring α where

class IsNonAssocSemiring (α: Type*) [AddMonoidWithOneOps α] [Mul α] extends IsNonUnitalNonAssocSemiring α, IsMulOneClass α, IsAddMonoidWithOne α: Prop

instance
  [AddMonoidWithOneOps α] [Mul α]
  [IsNonUnitalNonAssocSemiring α]
  [IsMulOneClass α]
  [IsAddMonoidWithOne α]
  : IsNonAssocSemiring α where
  natCast_zero := natCast_zero
  natCast_succ := natCast_succ
  ofNat_eq_natCast := IsAddMonoidWithOne.ofNat_eq_natCast

instance [SemiringOps α] [IsSemiring α] : IsNonAssocSemiring α where
  natCast_zero := natCast_zero
  natCast_succ := natCast_succ
  ofNat_eq_natCast := IsAddMonoidWithOne.ofNat_eq_natCast

class FieldOps (α: Type*) extends RingOps α,
  CheckedIntPow α (P := fun x => x ≠ 0),
  CheckedInvert α (P := fun x => x ≠ 0),
  CheckedDiv α (P := fun x => x ≠ 0) where

instance [RingOps α] [CheckedIntPow α (P := fun x => x ≠ 0)] [CheckedInvert α (P := fun x => x ≠ 0)] [CheckedDiv α (P := fun x => x ≠ 0)] : FieldOps α where

class IsNonCommField (α: Type*) [FieldOps α] extends IsRing α : Prop where
  mul_inv?_cancel: ∀(a: α) (h: a ≠ 0), a * a⁻¹? = 1
  div_eq_mul_inv?: ∀(a b: α) (h: b ≠ 0), a /? b = a * b⁻¹?
  zpow?_ofNat (n: ℕ) (a: α) : a ^? (n: ℤ) = a ^ n
  zpow?_negSucc (n: ℕ) (a: α) (h: a ≠ 0) : a ^? (Int.negSucc n) = (a⁻¹? ^ n.succ)

export IsNonCommField (
  mul_inv?_cancel
  div_eq_mul_inv?
  zpow?_ofNat
  zpow?_negSucc
)

class IsField (α: Type*) [FieldOps α] extends IsNonCommField α, IsCommMagma α : Prop where
