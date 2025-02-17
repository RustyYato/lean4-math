import Math.Function.Basic
import Math.Algebra.Group.Defs
import Math.Algebra.Module.Defs
import Math.Data.Like.Func

structure Matrix (α n m: Type*) where
  of :: toFun : n -> m -> α

namespace Matrix

def transpose : Matrix α n m -> Matrix α m n
| .of f => .of (flip f)

postfix:max "ᵀ" => transpose

attribute [coe] toFun

instance : FunLike (Matrix α n m) n (m -> α) where
  coe := toFun
  coe_inj := by
    intro a b eq
    cases a; congr

@[ext]
def ext (a b: Matrix α n m) : (∀i j, a i j = b i j) -> a = b := by
  intro h
  apply DFunLike.coe_inj
  ext i j
  apply h

instance [Add α] : Add (Matrix α n m) where
  add a b := .of fun i j => a i j + b i j

instance [Sub α] : Sub (Matrix α n m) where
  sub a b := .of fun i j => a i j - b i j

instance [Mul α] : SMul α (Matrix α n m) where
  smul r a := .of fun i j => r * a i j

instance [Neg α] : Neg (Matrix α n m) where
  neg a := .of fun i j => -a i j

instance [Zero α] : Zero (Matrix α n m) where
  zero := .of fun _ _ => 0

instance [SMul ℕ α] : SMul ℕ (Matrix α n m) where
  smul r a := .of fun i j => r • a i j

instance [SMul ℤ α] : SMul ℤ (Matrix α n m) where
  smul r a := .of fun i j => r • a i j

@[simp]
def add_elem [Add α] (a b: Matrix α n m) (i: n) (j: m) : (a + b) i j = a i j + b i j := rfl
@[simp]
def sub_elem [Sub α] (a b: Matrix α n m) (i: n) (j: m) : (a - b) i j = a i j - b i j := rfl
@[simp]
def smul_elem [Mul α] (x: α) (a: Matrix α n m) (i: n) (j: m) : (x • a) i j = x * a i j := rfl
@[simp]
def neg_elem [Neg α] (a: Matrix α n m) (i: n) (j: m) : (-a) i j = -a i j := rfl
@[simp]
def nsmul_elem [SMul ℕ α] (x: ℕ) (a: Matrix α n m) (i: n) (j: m) : (x • a) i j = x • a i j := rfl
@[simp]
def zsmul_elem [SMul ℤ α] (x: ℤ) (a: Matrix α n m) (i: n) (j: m) : (x • a) i j = x • a i j := rfl

instance [Add α] [IsAddCommMagma α] : IsAddCommMagma (Matrix α n m) where
  add_comm a b := by
    ext i j
    apply add_comm

instance [Add α] [IsAddSemigroup α] : IsAddSemigroup (Matrix α n m) where
  add_assoc a b c := by
    ext i j
    apply add_assoc

instance [Add α] [Zero α] [IsAddZeroClass α] : IsAddZeroClass (Matrix α n m) where
  zero_add a := by
    ext i j
    apply zero_add
  add_zero a := by
    ext i j
    apply add_zero

instance [AddMonoidOps α] [IsAddMonoid α] : IsAddMonoid (Matrix α n m) where
  zero_nsmul a := by
    ext i j
    apply zero_nsmul
  succ_nsmul n a := by
    ext i i
    apply succ_nsmul

instance [AddGroupOps α] [IsInvolutiveNeg α] : IsInvolutiveNeg (Matrix α n m) where
  neg_neg a := by
    ext i j
    apply neg_neg

instance [AddGroupOps α] [IsSubNegMonoid α] : IsSubNegMonoid (Matrix α n m) where
  sub_eq_add_neg a b := by
    ext i j
    apply sub_eq_add_neg
  zsmul_ofNat a b := by
    ext i j
    apply zsmul_ofNat
  zsmul_negSucc _ _ := by
    ext i j
    apply zsmul_negSucc

instance [AddGroupOps α] [IsSubtractionMonoid α] : IsSubtractionMonoid (Matrix α n m) where
  neg_add_rev _ _ := by
    ext i i
    apply neg_add_rev
  neg_eq_of_add_left {a b} h := by
    ext i j
    apply neg_eq_of_add_left
    show (a + b) i j = 0
    rw [h]
    rfl

instance instAddGroup [AddGroupOps α] [IsAddGroup α] : IsAddGroup (Matrix α n m) where
  neg_add_cancel a := by
    ext i j
    apply neg_add_cancel

instance [MonoidOps α] [IsMonoid α] : IsMulAction α (Matrix α n m) where
  one_smul a := by
    ext
    apply one_mul
  mul_smul a b c := by
    ext
    apply mul_assoc

instance [MonoidOps α] [AddMonoidOps α] [IsMonoid α] [IsAddMonoid α] [IsMulZeroClass α] [IsLeftDistrib α] : IsDistribMulAction α (Matrix α n m) where
  smul_zero a := by
    ext
    apply mul_zero
  smul_add a b c := by
    ext
    apply mul_add

instance [SemiringOps α] [IsSemiring α] : IsModule α (Matrix α n m) where
  add_smul a b c := by
    ext
    apply add_mul
  zero_smul a := by
    ext
    apply zero_mul

def diagonal [DecidableEq n] [Zero α] (f: n -> α) : Matrix α n n where
  toFun := fun i j => if i = j then f i else 0

instance [DecidableEq n] [One α] [Zero α] : One (Matrix α n n) where
  one := .diagonal fun _ => 1

instance [NatCast α] [Zero α] [DecidableEq n] : NatCast (Matrix α n n) where
  natCast x := diagonal fun _ => (x: α)
instance [IntCast α] [Zero α] [DecidableEq n] : IntCast (Matrix α n n) where
  intCast x := diagonal fun _ => (x: α)

instance [OfNat α n] [Zero α] [DecidableEq N] : OfNat (Matrix α N N) n where
  ofNat := diagonal fun _ => (OfNat.ofNat n)

@[simp]
def diagonal_mem [DecidableEq n] [Zero α] (f: n -> α) (i j: n) :
  diagonal f i j = if i = j then f i else 0 := rfl

@[simp]
def one_mem [DecidableEq n] [One α] [Zero α] (i j: n) :
 (1: Matrix α n n) i j = if i = j then 1 else 0 := rfl

@[simp]
def natCast_mem [DecidableEq N] [NatCast α] [Zero α] (n: ℕ) (i j: N) :
 (n: Matrix α N N) i j = if i = j then (n: α) else 0 := rfl
@[simp]
def intCast_mem [DecidableEq N] [IntCast α] [Zero α] (n: ℤ) (i j: N) :
 (n: Matrix α N N) i j = if i = j then (n: α) else 0 := rfl
@[simp]
def ofNat_mem [DecidableEq N] [OfNat α n] [Zero α] (i j: N) :
 (OfNat.ofNat n: Matrix α N N) i j = if i = j then OfNat.ofNat n else 0 := rfl

section

open Classical

instance instAddMonoidWithOne [AddMonoidWithOneOps α] [IsAddMonoidWithOne α]: IsAddMonoidWithOne (Matrix α N N) where
  natCast_zero := by
    ext i j
    simp
    split
    apply natCast_zero
    rfl
  natCast_succ n := by
    ext i j
    simp
    split
    rw [natCast_succ]
    rw [add_zero]
  ofNat_eq_natCast n := by
    ext i j
    simp
    split
    apply ofNat_eq_natCast
    rfl

instance instAddGroupWithOne [AddGroupWithOneOps α] [IsAddGroupWithOne α]: IsAddGroupWithOne (Matrix α N N) :=
  {
    instAddMonoidWithOne, instAddGroup with
    intCast_ofNat n := by
      ext i j
      simp
      split
      apply intCast_ofNat
      rfl
    intCast_negSucc n := by
      ext i j
      simp
      split
      apply intCast_negSucc
      rw [neg_zero]
  }

end

end Matrix
