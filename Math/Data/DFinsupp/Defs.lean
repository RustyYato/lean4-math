import Math.Data.DFinsupp.Support
import Math.Algebra.Group.Hom
import Math.Algebra.Module.Defs
import Math.Data.Trunc

structure DFinsupp (α: ι -> Type*) (S: Type*) [FiniteSupportOps S ι] [∀i, Zero (α i)] where
  toFun (i: ι): α i
  spec: Trunc { set : S // ∀(i: ι), toFun i ≠ 0 -> i ∈ set }

namespace DFinsupp

variable {α: ι -> Type*} [DecidableEq ι]

section Basics

variable [∀i, Zero (α i)] [FiniteSupportOps S ι]

instance : DFunLike (DFinsupp α S) ι α where
  coe f x := f.toFun x
  coe_inj := by
    rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    simp
    suffices f = g by
      cases this
      apply And.intro rfl
      apply Subsingleton.helim
      rfl
    ext; apply congrFun h

@[ext]
def ext (f g: DFinsupp α S) : (∀i, f i = g i) -> f = g := DFunLike.ext f g

@[simp]
def toFun_eq_coe (f: DFinsupp α S) : f.toFun = f := rfl

instance : Zero (DFinsupp α S) where
  zero := {
    toFun _ := 0
    spec := Trunc.mk {
      val := default
      property := nofun
    }
  }

@[simp]
def apply_zero (i: ι) : (0: DFinsupp α S) i = 0 := rfl

end Basics

section

variable [FiniteSupport S ι]

def single [∀i, Zero (α i)] (i: ι) (a: α i) : DFinsupp α S where
  toFun j :=
    if h:i = j then
      cast (by rw [h]) a
    else
      0
  spec := Trunc.mk {
    val := FiniteSupport.singleton i
    property := by
      intro j h
      simp at h
      obtain ⟨rfl, ne⟩ := h
      apply FiniteSupport.mem_singleton
  }

@[simp]
def apply_single [∀i, Zero (α i)] (i j: ι) (a: α i) : single (S := S) i a j = if h:i = j then cast (by rw [h]) a else 0 := rfl

def copy [∀i, Zero (α i)] (f: DFinsupp α S) (g: ∀i, α i) (h: f = g) : DFinsupp α S where
  toFun := g
  spec := do
      let ⟨fset, fspec⟩ ← f.spec
      return {
        val := fset
        property := by
          rw [←h]
          apply fspec
      }

@[simp]
def apply_copy [∀i, Zero (α i)] (f: DFinsupp α S) (g: ∀i, α i) (h: f = g) (i: ι) : f.copy g h i = g i := rfl

end

section Algebra

variable [FiniteSupport S ι]

instance [∀i, Zero (α i)]  [∀i, Add (α i)] [∀i, IsAddZeroClass (α i)] : Add (DFinsupp α S) where
  add f g := {
    toFun i := f i + g i
    spec := do
      let ⟨fset, fspec⟩ ← f.spec
      let ⟨gset, gspec⟩ ← g.spec
      return {
        val := fset ⊔ gset
        property i ne := by
          by_cases h:g i = 0
          simp [h] at ne
          apply FiniteSupport.mem_max
          apply fspec
          assumption
          rw [max_comm]
          apply FiniteSupport.mem_max
          apply gspec
          assumption
      }
  }

instance [∀i, Zero (α i)]  [∀i, Mul (α i)] [∀i, IsMulZeroClass (α i)] : Mul (DFinsupp α S) where
  mul f g := {
    toFun i := f i * g i
    spec := do
      let ⟨fset, fspec⟩ ← f.spec
      let ⟨gset, gspec⟩ ← g.spec
      return {
        val := fset ⊓ gset
        property i ne := by
          apply FiniteSupport.mem_min
          apply fspec
          simp; intro h
          simp [h] at ne
          apply gspec
          simp; intro h
          simp [h] at ne
      }
  }

instance (priority := 2000) [∀i, AddMonoidOps (α i)] [∀i, IsAddMonoid (α i)] : SMul ℕ (DFinsupp α S) where
  smul n f := {
    toFun i := n • f i
    spec := do
      let ⟨fset, fspec⟩ ← f.spec
      return {
        val := if n = 0 then default else fset
        property i ne := by
          match n with
          | 0 =>
          simp [zero_nsmul] at ne
          | n + 1 =>
          by_cases h:f i = 0
          simp [h] at ne
          rw [if_neg]
          apply fspec
          assumption
          omega
      }
  }

instance (priority := 2000) [∀i, AddGroupOps (α i)] [∀i, IsSubNegMonoid (α i)] [∀i, IsNegZeroClass (α i)] : SMul ℤ (DFinsupp α S) where
  smul n f := {
    toFun i := n • f i
    spec := do
      let ⟨fset, fspec⟩ ← f.spec
      return {
        val := if n = 0 then default else fset
        property i ne := by
          match n with
          | 0 =>
          simp [zero_nsmul] at ne
          | Int.ofNat (n + 1) | Int.negSucc n =>
          by_cases h:f i = 0
          simp [h] at ne
          rw [if_neg]
          apply fspec
          assumption
          simp
          try omega
      }
  }

instance [∀i, Zero (α i)] [∀i, Neg (α i)] [∀i, IsNegZeroClass (α i)] : Neg (DFinsupp α S) where
  neg f := {
    toFun i := -f i
    spec := do
      let ⟨fset, fspec⟩ ← f.spec
      return {
        val := fset
        property i ne := by
          apply fspec
          simp; intro h; simp [h] at ne
      }
  }

instance [∀i, AddGroupOps (α i)] [∀i, IsSubNegMonoid (α i)] [∀i, IsNegZeroClass (α i)]: Sub (DFinsupp α S) where
  sub f g := (f + -g).copy (fun i => f i  - g i) (by
    ext i
    symm; apply sub_eq_add_neg)

instance (priority := 900)
  [MonoidOps R] [IsMonoid R] [∀i, SMul R (α i)]
  [∀i, AddMonoidOps (α i)] [∀i, IsAddMonoid (α i)]
  [∀i, IsDistribMulAction R (α i)] : SMul R (DFinsupp α S) where
  smul n f := {
    toFun i := n • f i
    spec := do
      let ⟨fset, fspec⟩ ← f.spec
      return {
        val := fset
        property i ne := by
          apply fspec
          simp; intro h; simp [h] at ne
      }
  }

instance (priority := 1100) [∀i, AddMonoidOps (α i)] [∀i, IsAddMonoid (α i)] : AddMonoidOps (DFinsupp α S) := inferInstance
instance (priority := 1100) [∀i, AddGroupOps (α i)] [∀i, IsAddGroup (α i)] : AddGroupOps (DFinsupp α S) := inferInstance

@[simp] def apply_add [∀i, Zero (α i)] [∀i, Add (α i)] [∀i, IsAddZeroClass (α i)] (f g: DFinsupp α S) (i: ι) : (f + g) i = f i + g i := rfl
@[simp] def apply_mul [∀i, Zero (α i)] [∀i, Mul (α i)] [∀i, IsMulZeroClass (α i)] (f g: DFinsupp α S) (i: ι) : (f * g) i = f i * g i := rfl
@[simp] def apply_nsmul [∀i, AddMonoidOps (α i)] [∀i, IsAddMonoid (α i)] (n: ℕ) (f: DFinsupp α S) (i: ι) : (n • f) i = n • f i := rfl
@[simp] def apply_zsmul [∀i, AddGroupOps (α i)] [∀i, IsSubNegMonoid (α i)] [∀i, IsNegZeroClass (α i)] (n: ℤ) (f: DFinsupp α S) (i: ι) : (n • f) i = n • f i := rfl
@[simp] def apply_neg [∀i, Zero (α i)] [∀i, Neg (α i)] [∀i, IsNegZeroClass (α i)] (f: DFinsupp α S) (i: ι) : (-f) i = -f i := rfl
@[simp] def apply_sub [∀i, AddGroupOps (α i)] [∀i, IsSubNegMonoid (α i)] [∀i, IsNegZeroClass (α i)] (f g: DFinsupp α S) (i: ι) : (f - g) i = f i - g i := rfl
@[simp] def apply_smul
  [MonoidOps R] [IsMonoid R] [∀i, SMul R (α i)]
  [∀i, AddMonoidOps (α i)] [∀i, IsAddMonoid (α i)]
  [∀i, IsDistribMulAction R (α i)] (r: R) (f: DFinsupp α S) (i: ι) : (r • f) i = r • f i := rfl

instance [∀i, Zero (α i)] [∀i, Add (α i)] [∀i, IsAddZeroClass (α i)] [∀i, IsAddCommMagma (α i)]
  : IsAddCommMagma (DFinsupp α S) where
  add_comm _ _ := by ext; apply add_comm

instance [∀i, Zero (α i)] [∀i, Mul (α i)] [∀i, IsMulZeroClass (α i)] [∀i, IsCommMagma (α i)]
  : IsCommMagma (DFinsupp α S) where
  mul_comm _ _ := by ext; apply mul_comm

instance [∀i, AddMonoidOps (α i)] [∀i, IsAddMonoid (α i)] : IsAddMonoid (DFinsupp α S) where
  add_assoc _ _ _ := by ext; apply add_assoc
  zero_add _ := by ext; apply zero_add
  add_zero _ := by ext; apply add_zero
  zero_nsmul _ := by ext; apply zero_nsmul
  succ_nsmul _ _ := by ext; apply succ_nsmul

instance [∀i, AddGroupOps (α i)] [∀i, IsAddGroup (α i)] : IsAddGroup (DFinsupp α S) where
  sub_eq_add_neg _ _ := by ext; apply sub_eq_add_neg
  neg_add_cancel _ := by ext; apply neg_add_cancel
  zsmul_ofNat _ _ := by ext; apply zsmul_ofNat
  zsmul_negSucc _ _ := by ext; apply zsmul_negSucc

instance
  [∀i, Zero (α i)] [∀i, Add (α i)] [∀i, IsAddZeroClass (α i)]
  [∀i, Mul (α i)] [∀i, IsMulZeroClass (α i)] [∀i, IsLeftDistrib (α i)] :
  IsLeftDistrib (DFinsupp α S) where
  mul_add _ _ _ := by ext; apply mul_add

instance
  [∀i, Zero (α i)] [∀i, Add (α i)] [∀i, IsAddZeroClass (α i)]
  [∀i, Mul (α i)] [∀i, IsMulZeroClass (α i)] [∀i, IsRightDistrib (α i)] :
  IsRightDistrib (DFinsupp α S) where
  add_mul _ _ _ := by ext; apply add_mul

instance [∀i, Zero (α i)] [∀i, Mul (α i)] [∀i, IsMulZeroClass (α i)] [∀i, IsSemigroup (α i)] : IsSemigroup (DFinsupp α S) where
  mul_assoc _ _ _ := by ext; apply mul_assoc

instance [∀i, Zero (α i)] [∀i, Mul (α i)] [∀i, IsMulZeroClass (α i)] : IsMulZeroClass (DFinsupp α S) where
  mul_zero _ := by ext; apply mul_zero
  zero_mul _ := by ext; apply zero_mul

instance (priority := 1100) [∀i, AddGroupOps (α i)] [∀i, IsAddGroup (α i)]
  [∀i, Mul (α i)] [∀i, IsNonUnitalNonAssocRing (α i)] : IsNonUnitalNonAssocRing (DFinsupp α S) where

instance (priority := 1100) [∀i, AddGroupOps (α i)] [∀i, IsAddGroup (α i)]
  [∀i, Mul (α i)] [∀i, IsNonUnitalRing (α i)] : IsNonUnitalRing (DFinsupp α S) where

instance
  [MonoidOps R] [IsMonoid R] [∀i, SMul R (α i)]
  [∀i, AddMonoidOps (α i)] [∀i, IsAddMonoid (α i)]
  [∀i, IsDistribMulAction R (α i)] : IsDistribMulAction R (DFinsupp α S) where
  one_smul _ := by ext; apply one_smul
  mul_smul _ _ _ := by ext; apply mul_smul
  smul_zero _ := by ext; apply smul_zero
  smul_add _ _ _ := by ext; apply smul_add

instance
  [SemiringOps R] [IsSemiring R] [∀i, SMul R (α i)]
  [∀i, AddMonoidOps (α i)] [∀i, IsAddMonoid (α i)] [∀i, IsAddCommMagma (α i)]
  [∀i, IsModule R (α i)] : IsModule R (DFinsupp α S) where
  add_smul _ _ _ := by ext; apply add_smul
  zero_smul _ := by ext; apply zero_smul

end Algebra

end DFinsupp
