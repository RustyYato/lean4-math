import Math.Data.DFinsupp.Algebra

structure DirectSum (α: ι -> Type*) [∀i, Zero (α i)] where
  ofFinsupp :: toFinsupp : DFinsupp α (Finset ι)

section Syntax

open Lean
open TSyntax.Compat

macro "⊕ " xs:explicitBinders ", " b:term:60 : term => expandExplicitBinders ``DirectSum xs b

@[app_unexpander DirectSum] def unexpand_DirectSum : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => ⊕ $xs:binderIdent*, $b) => `(⊕ $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                     => `(⊕ $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)              => `(⊕ ($x:ident : $t), $b)
  | _                                              => throw ()

end Syntax
namespace DirectSum

variable {α: ι -> Type*} [DecidableEq ι]

section

variable [∀i, Zero (α i)]

instance : Zero (⊕i, α i) where
  zero := ⟨0⟩

instance : DFunLike (⊕i, α i) ι α where
  coe f := f.toFinsupp

@[ext]
def ext (a b: ⊕i, α i) : (∀i, a i = b i) -> a = b := DFunLike.ext _ _

@[simp] def apply_zero (i: ι) : (0: ⊕i, α i) i = 0 := rfl

end

section

variable [∀i, AddMonoidOps (α i)] [∀i, IsAddMonoid (α i)]

instance : Add (⊕i, α i) where
  add a b := ⟨a.1 + b.1⟩

instance : SMul ℕ (⊕i, α i) where
  smul n a := ⟨n • a.1⟩

instance : IsAddMonoid (⊕i, α i) where
  add_assoc _ _ _ := by ext; apply add_assoc
  add_zero _ := by ext; apply add_zero
  zero_add _ := by ext; apply zero_add
  zero_nsmul _ := by ext; apply zero_nsmul
  succ_nsmul _ _ := by ext; apply succ_nsmul

instance [∀i, IsAddCommMagma (α i)] : IsAddCommMagma (⊕i, α i) where
  add_comm _ _ := by ext; apply add_comm

@[simp] def apply_add (a b: ⊕i, α i) : (a + b) i = a i + b i := rfl
@[simp] def apply_nsmul (n: ℕ) (a: ⊕i, α i) : (n • a) i = n • a i := rfl

end

section

variable [∀i, AddGroupOps (α i)] [∀i, IsAddGroup (α i)]

instance : Neg (⊕i, α i) where
  neg a := ⟨-a.1⟩

instance : Sub (⊕i, α i) where
  sub a b := ⟨a.1 - b.1⟩

instance : SMul ℤ (⊕i, α i) where
  smul n a := ⟨n • a.1⟩

instance : IsAddGroup (⊕i, α i) where
  sub_eq_add_neg _ _ := by ext; apply sub_eq_add_neg
  zsmul_ofNat _ _ := by ext; apply zsmul_ofNat
  zsmul_negSucc _ _ := by ext; apply zsmul_negSucc
  neg_add_cancel _ := by ext; apply neg_add_cancel

@[simp] def apply_neg (a: ⊕i, α i) : (-a) i = -a i := rfl
@[simp] def apply_sub (a b: ⊕i, α i) : (a - b) i = a i - b i := rfl
@[simp] def apply_zsmul (n: ℤ) (a: ⊕i, α i) : (n • a) i = n • a i := rfl

end

section

variable
  [SemiringOps R] [IsSemiring R]
  [∀i, AddMonoidOps (α i)] [∀i, IsAddMonoid (α i)] [∀i, IsAddCommMagma (α i)]
  [∀i, SMul R (α i)] [∀i, IsModule R (α i)]

instance : SMul R (⊕i, α i) where
  smul r a := ⟨r • a.1⟩

instance : IsModule R (⊕i, α i) where
  one_smul _ := by ext; apply one_smul
  smul_zero _ := by ext; apply smul_zero
  zero_smul _ := by ext; apply zero_smul
  mul_smul _ _ _ := by ext; apply mul_smul
  smul_add _ _ _ := by ext; apply smul_add
  add_smul _ _ _ := by ext; apply add_smul

@[simp] def apply_smul (n: R) (a: ⊕i, α i) : (n • a) i = n • a i := rfl

end

end DirectSum
