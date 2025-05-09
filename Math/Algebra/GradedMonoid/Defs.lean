import Math.Algebra.Monoid.Defs

def GradedMonoid {ι: Type*} : (ι -> Type*) -> Type _ := Sigma

namespace GradedMonoid

variable {ι: Type*} {A: ι -> Type*}

def mk : A i -> GradedMonoid A := Sigma.mk i

@[ext]
def ext (a b: GradedMonoid A) : a.fst = b.fst -> HEq a.snd b.snd -> a = b := Sigma.ext

def get_cast (a: GradedMonoid A) (i: ι) (h: a.fst = i) : A i := h ▸ a.snd

@[simp]
def mk_get_cast (a: GradedMonoid A) (i: ι) (h: a.fst = i) : mk (a.get_cast i h) = a := by
  ext
  rw [h]; rfl
  subst i
  rfl

def mk_inj (a: A i) (b: A j) : mk a = mk b -> i = j ∧ HEq a b := by
  intro h; cases h; trivial

end GradedMonoid

section Classes

variable {ι: Type*} (A: ι -> Type*)

class GOne [Zero ι] where
  gOne: A 0

class GMul [Add ι] where
  gMul {n m: ι}: A n -> A m -> A (n + m)

class GPow [SMul ℕ ι] where
  gPow (n: ℕ) {i: ι}: A i -> A (n • i)

class GMonoidOps [AddMonoidOps ι] extends GOne A, GMul A, GPow A where
instance [AddMonoidOps ι] [GOne A] [GMul A] [GPow A] : GMonoidOps A where

instance [Zero ι] [GOne A] : One (GradedMonoid A) where
  one := .mk GOne.gOne

instance [Add ι] [GMul A] : Mul (GradedMonoid A) where
  mul x y := .mk (GMul.gMul x.2 y.2)

instance [SMul ℕ ι] [GPow A] : Pow (GradedMonoid A) ℕ where
  pow x n := .mk (GPow.gPow n x.2)

abbrev IsGMonoid [AddMonoidOps ι] [IsAddMonoid ι] [GMonoidOps A] :=
  IsMonoid (GradedMonoid A)

abbrev IsGCommMagma [Add ι] [IsAddCommMagma ι] [GMul A] :=
  IsCommMagma (GradedMonoid A)

def instGPow [AddMonoidOps ι] [IsAddMonoid ι] [GOne A] [GMul A] : GPow A where
  gPow n i a := (npowRec n (GradedMonoid.mk a)).get_cast _ <| by
    induction n with
    | zero => rw [zero_nsmul]; rfl
    | succ n ih => rw [succ_nsmul, ←ih]; rfl

namespace GradedMonoid

variable [AddMonoidOps ι] [IsAddMonoid ι] [GMonoidOps A] [IsGMonoid A]

def fst_one : (1: GradedMonoid A).fst = 0 := rfl
def fst_mul (a b: GradedMonoid A) : (a * b).fst = a.fst + b.fst := rfl
def fst_pow (a: GradedMonoid A) (n: ℕ) : (a ^ n).fst = n • a.fst := rfl

end GradedMonoid

end Classes

section Instances

instance [Zero ι] [One R] : GOne (fun _: ι => R) where
  gOne := 1

instance [Add ι] [Mul R] : GMul (fun _: ι => R) where
  gMul a b := a * b

instance [SMul ℕ ι] [Pow R ℕ] : GPow (fun _: ι => R) where
  gPow n {_} a := a ^ n

instance [AddMonoidOps ι] [IsAddMonoid ι] [MonoidOps R] [IsMonoid R] : IsGMonoid (fun _: ι => R) where
  mul_assoc a b c := by
    ext; apply add_assoc
    apply heq_of_eq
    apply mul_assoc
  one_mul a := by
    ext; apply zero_add
    apply heq_of_eq
    apply one_mul
  mul_one a := by
    ext; apply add_zero
    apply heq_of_eq
    apply mul_one
  npow_zero a := by
    ext; apply zero_nsmul
    apply heq_of_eq
    apply npow_zero
  npow_succ n a := by
    ext; apply succ_nsmul
    apply heq_of_eq
    apply npow_succ

instance [Add ι] [IsAddCommMagma ι] [Mul R] [IsCommMagma R] : IsGCommMagma (fun _: ι => R) where
  mul_comm a b := by
    ext; apply add_comm
    apply heq_of_eq
    apply mul_comm

end Instances
