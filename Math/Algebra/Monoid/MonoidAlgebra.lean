import Math.Data.FinSupp.Defs

structure AddMonoidAlgebra (α β S: Type*) [Zero β] [FiniteSupportSet S α] where
  ofFinsupp ::
  toFinsupp : Finsupp α β S

namespace AddMonoidAlgebra

variable [FiniteSupportSet S α]

instance [Zero β] : FunLike (AddMonoidAlgebra α β S) α β where
  coe f := f.toFinsupp
  coe_inj := by
    intro a b eq; cases a ; cases b; congr
    apply DFunLike.coe_inj
    assumption

@[ext]
def ext [Zero β] (f g: AddMonoidAlgebra α β S) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _

instance [Zero β] : Zero (AddMonoidAlgebra α β S) where
  zero := ⟨0⟩

@[simp] def apply_zero [Zero β] (x: α) : (0: AddMonoidAlgebra α β S) x = 0 := rfl

def single [Zero β] [DecidableEq α] (a: α) (b: β) : AddMonoidAlgebra α β S where
  toFinsupp := .single a b

def apply_single [Zero β] [DecidableEq α] {a: α} {b: β} (x: α) : single (S := S) a b x = if x = a then b else 0 := rfl

instance [Zero β] [Add β] [IsAddZeroClass β] : Add (AddMonoidAlgebra α β S) where
  add f g := ⟨f.toFinsupp + g.toFinsupp⟩

instance [Zero β] [Neg β] [IsNegZeroClass β] : Neg (AddMonoidAlgebra α β S) where
  neg f := ⟨-f.toFinsupp⟩

instance [AddMonoidOps β] [IsAddMonoid β] : SMul ℕ (AddMonoidAlgebra α β S) where
  smul n f := ⟨n • f.toFinsupp⟩

instance [AddGroupOps β] [IsNegZeroClass β] [IsSubNegMonoid β] : Sub (AddMonoidAlgebra α β S) where
  sub f g := ⟨f.toFinsupp - g.toFinsupp⟩

instance [AddGroupOps β] [IsNegZeroClass β] [IsSubNegMonoid β] : SMul ℤ (AddMonoidAlgebra α β S) where
  smul n f := ⟨n • f.toFinsupp⟩

@[simp] def apply_add [Zero β] [Add β] [IsAddZeroClass β] (f g: Finsupp α β S) (x: α) : (f + g) x = f x + g x := rfl

@[simp] def apply_neg [Zero β] [Neg β] [IsNegZeroClass β] (f: Finsupp α β S) (x: α) : (-f) x = -f x := rfl

@[simp] def apply_nsmul [AddMonoidOps β] [IsAddMonoid β] (n: ℕ) (f: Finsupp α β S) (x: α) : (n • f) x = n • f x := rfl

@[simp] def apply_sub [AddGroupOps β] [IsNegZeroClass β] [IsSubNegMonoid β] (f g: Finsupp α β S) (x: α) : (f - g) x = f x - g x := rfl

@[simp] def apply_zsmul [AddGroupOps β] [IsNegZeroClass β] [IsSubNegMonoid β] (n: ℤ) (f: Finsupp α β S) (x: α) : (n • f) x = n • f x := rfl

instance [Zero β] [Add β] [IsAddZeroClass β] : IsAddZeroClass (Finsupp α β S) where
  zero_add _ := by ext; simp
  add_zero _ := by ext; simp

instance [Zero β] [Add β] [IsAddZeroClass β] [IsAddSemigroup β] : IsAddSemigroup (Finsupp α β S) where
  add_assoc a b c := by ext; simp [add_assoc]

instance [AddMonoidOps β] [IsAddMonoid β] : IsAddMonoid (Finsupp α β S) where
  zero_nsmul a := by ext; simp
  succ_nsmul n a := by ext x; simp [succ_nsmul]

instance [AddMonoidOps β] [IsAddMonoid β] : IsAddMonoid (Finsupp α β S) where
  zero_nsmul a := by ext; simp
  succ_nsmul n a := by ext x; simp [succ_nsmul]

instance [Zero β] [Neg β] [IsNegZeroClass β] : IsNegZeroClass (Finsupp α β S) where
  neg_zero := by ext x; simp

instance [AddGroupOps β] [IsNegZeroClass β] [IsSubNegMonoid β] : IsSubNegMonoid (Finsupp α β S) where
  sub_eq_add_neg f g := by ext; simp [sub_eq_add_neg]
  zsmul_ofNat n f := by ext; simp [zsmul_ofNat]
  zsmul_negSucc n f := by ext; simp [zsmul_negSucc]

instance [AddGroupOps β] [IsAddGroup β] : IsAddGroup (Finsupp α β S) where
  neg_add_cancel a := by ext; simp [neg_add_cancel]

end AddMonoidAlgebra
