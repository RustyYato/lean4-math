import Math.Algebra.Semigroup.Defs

def nsmulRec [Zero α] [Add α] : ℕ -> α -> α
| 0, _ => 0
| n + 1, a => nsmulRec n a + a

def npowRec [One α] [Mul α] : ℕ -> α -> α := nsmulRec (α := AddOfMul α)

def instNSMulrec [Zero α] [Add α]: SMul ℕ α := ⟨nsmulRec⟩
def instNPowrec [One α] [Mul α]: Pow α ℕ := ⟨flip npowRec⟩

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

class IsAddMonoid (α: Type*) [AddMonoidOps α] : Prop extends IsAddSemigroup α, IsAddZeroClass α where
  zero_nsmul (a: α) : 0 • a = 0 := by intros; rfl
  succ_nsmul (n: ℕ) (a: α) : (n + 1) • a = n • a + a := by intros; rfl
class IsMonoid (α: Type*) [MonoidOps α] : Prop extends IsSemigroup α, IsMulOneClass α where
  npow_zero (a: α) : a ^ 0 = 1 := by intros; rfl
  npow_succ (n: ℕ) (a: α) : a ^ (n + 1) = a ^ n * a := by intros; rfl

variable [AddMonoidOps α] [MonoidOps α] [IsAddMonoid α] [IsMonoid α]

@[simp] def zero_nsmul (a: α) : 0 • a = 0 := IsAddMonoid.zero_nsmul _
def succ_nsmul (n: ℕ) (a: α) : (n + 1) • a = n • a + a := IsAddMonoid.succ_nsmul _ _

@[simp] def npow_zero (a: α) : a ^ 0 = 1 := IsMonoid.npow_zero _
def npow_succ (n: ℕ) (a: α) : a ^ (n + 1) = a ^ n * a := IsMonoid.npow_succ _ _

@[simp] def zero_npow_zero [Zero α] [IsMulZeroClass α] : (0: α) ^ 0 = 1 := npow_zero _
@[simp] def zero_npow_succ [Zero α] [IsMulZeroClass α] (n: ℕ) : (0: α) ^ (n + 1) = 0 := by simp [npow_succ]


instance : IsAddMonoid (AddOfMul α) where
  zero_nsmul := npow_zero (α := α)
  succ_nsmul := npow_succ (α := α)
instance : IsMonoid (MulOfAdd α) where
  npow_zero := zero_nsmul (α := α)
  npow_succ := succ_nsmul (α := α)
instance : IsMonoid αᵃᵒᵖ := inferInstanceAs (IsMonoid α)
instance : IsAddMonoid αᵐᵒᵖ := inferInstanceAs (IsAddMonoid α)

@[simp] def nsmul_zero (a: ℕ) : a • (0: α) = 0 := by
  induction a with
  | zero => rw [zero_nsmul]
  | succ a ih => rw [succ_nsmul, ih, add_zero]
@[simp] def one_npow (a: ℕ) : (1: α) ^ a = 1 := nsmul_zero (α := AddOfMul α) _

@[simp] def one_nsmul (a: α) : 1 • a = a := by rw [succ_nsmul, zero_nsmul, zero_add]
@[simp] def npow_one (a: α) : a ^ 1 = a := one_nsmul (α := AddOfMul α) _

def nsmul_eq_nsmulRec (n: ℕ) (a: α) : n • a = nsmulRec n a := by
  induction n with
  | zero => rw [zero_nsmul]; rfl
  | succ n ih => rw [succ_nsmul, ih]; rfl

def npow_eq_npowRec (n: ℕ) (a: α) : a ^ n = npowRec n a :=
  nsmul_eq_nsmulRec (α := AddOfMul α) _ _

def succ_nsmul' (n: ℕ) (a: α) : (n + 1) • a = a + n • a := by
  have : IsAddSemigroup α := IsAddMonoid.toIsAddSemigroup
  induction n with
  | zero =>
    rw [zero_nsmul, add_zero, succ_nsmul, zero_nsmul, zero_add]
  | succ n ih => rw [succ_nsmul n, ←add_assoc, ←ih, succ_nsmul (n + 1)]
def npow_succ' (n: ℕ) (a: α) : a ^ (n + 1) = a * a ^ n :=
  succ_nsmul' (α := AddOfMul α) _ _

instance : IsAddMonoid αᵃᵒᵖ where
  zero_nsmul := zero_nsmul (α := α)
  succ_nsmul := succ_nsmul' (α := α)
instance : IsMonoid αᵐᵒᵖ where
  npow_zero := npow_zero (α := α)
  npow_succ := npow_succ' (α := α)

def add_nsmul (n m: ℕ) (a: α) : (n + m) • a = n • a + m • a := by
  induction m with
  | zero => rw [Nat.add_zero, zero_nsmul, add_zero]
  | succ m ih => rw [Nat.add_succ, succ_nsmul, succ_nsmul, ←add_assoc, ih]
def npow_add (n m: ℕ) (a: α) : a ^ (n + m) = a ^ n * a ^ m :=
  add_nsmul (α := AddOfMul α) _ _ _

def nsmul_add [IsAddCommMagma α] (n: ℕ) (x y: α) : n • (x + y) = n • x + n • y := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, zero_nsmul, add_zero]
  | succ n ih =>
    rw [succ_nsmul, ih, add_assoc, add_comm _ (x + y), ←add_assoc, ←add_assoc, ←succ_nsmul, add_assoc, ←succ_nsmul']

def mul_npow [IsCommMagma α] (n: ℕ) (x y: α) : (x * y) ^ n = x ^ n * y ^ n :=
  nsmul_add (α := AddOfMul α) _ _ _

def mul_nsmul (n m: ℕ) (x: α) : (m * n) • x = m • n • x := by
  induction m with
  | zero => rw [Nat.zero_mul, zero_nsmul, zero_nsmul]
  | succ m ih => rw [succ_nsmul, Nat.succ_mul, add_nsmul, ih]

def npow_mul (n m: ℕ) (x: α) : x ^ (m * n) = (x ^ n) ^ m :=
  mul_nsmul (α := AddOfMul α) _ _ _

def npow_two (x: α) : x ^ 2 = x * x := by
  rw [npow_succ, npow_succ, npow_zero, one_mul]

def eq_zero_iff_left (a: α) : a = 0 ↔ ∀b, a + b = b := by
  apply Iff.intro
  rintro rfl
  intro x ; rw [zero_add]
  intro h
  have := h 0
  rwa [add_zero] at this
def eq_zero_iff_right (a: α) : a = 0 ↔ ∀b, b + a = b := by
  apply Iff.intro
  rintro rfl
  intro x ; rw [add_zero]
  intro h
  have := h 0
  rwa [zero_add] at this

def eq_one_iff_left (a: α) : a = 1 ↔ ∀b, a * b = b :=
  eq_zero_iff_left (α := AddOfMul α) _
def eq_one_iff_right (a: α) : a = 1 ↔ ∀b, b * a = b :=
  eq_zero_iff_right (α := AddOfMul α) _

instance (n: ℕ) (x a: α) [IsAddCommutes a x] : IsAddCommutes (n • a) x where
  add_commutes := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [succ_nsmul, add_assoc, add_comm _ x, ←add_assoc, ih, add_assoc]

instance (n: ℕ) (x a: α) [IsAddCommutes x a] : IsAddCommutes x (n • a) := inferInstance
instance (n: ℕ) (a: α) : IsAddCommutes a (n • a) := inferInstance
instance (n: ℕ) (a: α) : IsAddCommutes (n • a) a := inferInstance
instance (n m: ℕ) (a: α) : IsAddCommutes (n • a) (m • a) := inferInstance

instance (n: ℕ) (x a: α) [IsCommutes a x] : IsCommutes (a ^ n) x where
  mul_commutes := add_comm (n • AddOfMul.mk a) (AddOfMul.mk x)

instance (n: ℕ) (x a: α) [IsCommutes x a] : IsCommutes x (a ^ n) := inferInstance
instance (n: ℕ) (a: α) : IsCommutes a (a ^ n) := inferInstance
instance (n: ℕ) (a: α) : IsCommutes (a ^ n) a := inferInstance
instance (n m: ℕ) (a: α) : IsCommutes (a ^ n) (a ^ m) := inferInstance

instance : IsAddCommMagma Nat where
  add_comm := Nat.add_comm

instance : IsCommMagma Nat where
  mul_comm := Nat.mul_comm

instance : IsAddMonoid Nat where
  add_assoc := Nat.add_assoc
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero
  zero_nsmul := Nat.zero_mul
  succ_nsmul := Nat.succ_mul

instance : IsMonoid Nat where
  mul_assoc := Nat.mul_assoc
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one

instance : IsMulZeroClass Nat where
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero

instance : IsAddCommMagma Int where
  add_comm := Int.add_comm

instance : IsCommMagma Int where
  mul_comm := Int.mul_comm

instance : SMul ℕ ℤ where
  smul a b := a * b

instance : IsAddMonoid Int where
  add_assoc := Int.add_assoc
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  zero_nsmul := Int.zero_mul
  succ_nsmul := by
    intro n a
    show (n + 1) * a = _
    rw [Int.add_mul, Int.one_mul]
    rfl

instance : IsMonoid Int where
  mul_assoc := Int.mul_assoc
  one_mul := Int.one_mul
  mul_one := Int.mul_one

instance : IsMulZeroClass Int where
  zero_mul := Int.zero_mul
  mul_zero := Int.mul_zero
