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

instance [AddGroupOps α] [IsAddGroup α] : IsAddGroup (Matrix α n m) where
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

end Matrix
