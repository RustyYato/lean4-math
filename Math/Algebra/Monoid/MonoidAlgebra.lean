import Math.Data.FinSupp.Defs
import Math.Data.FinSupp.Algebra
import Math.AxiomBlame

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

def toFinsupp_inj [Zero β] : Function.Injective (toFinsupp (α := α) (β := β) (S := S)) := by
  intro a b eq; cases a; congr

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

@[simp]
def single_zero [DecidableEq α] [Zero β] (a: α) : single (S := S) a (0: β) = 0 := by
  ext; simp
  rw [apply_single]
  split <;> rfl

def add_def [Zero β] [Add β] [IsAddZeroClass β] (f g: AddMonoidAlgebra α β S) : f + g = ⟨f.toFinsupp + g.toFinsupp⟩ := rfl
def add_def' [Zero β] [Add β] [IsAddZeroClass β] (f g: AddMonoidAlgebra α β S) : f.toFinsupp + g.toFinsupp = (f + g).toFinsupp := rfl
@[simp] def apply_add [Zero β] [Add β] [IsAddZeroClass β] (f g: AddMonoidAlgebra α β S) (x: α) : (f + g) x = f x + g x := rfl

@[simp] def apply_neg [Zero β] [Neg β] [IsNegZeroClass β] (f: AddMonoidAlgebra α β S) (x: α) : (-f) x = -f x := rfl

@[simp] def apply_nsmul [AddMonoidOps β] [IsAddMonoid β] (n: ℕ) (f: AddMonoidAlgebra α β S) (x: α) : (n • f) x = n • f x := rfl

@[simp] def apply_sub [AddGroupOps β] [IsNegZeroClass β] [IsSubNegMonoid β] (f g: AddMonoidAlgebra α β S) (x: α) : (f - g) x = f x - g x := rfl

@[simp] def apply_zsmul [AddGroupOps β] [IsNegZeroClass β] [IsSubNegMonoid β] (n: ℤ) (f: AddMonoidAlgebra α β S) (x: α) : (n • f) x = n • f x := rfl

instance [Zero β] [Add β] [IsAddZeroClass β] : IsAddZeroClass (AddMonoidAlgebra α β S) where
  zero_add _ := by ext; simp
  add_zero _ := by ext; simp

instance [Zero β] [Add β] [IsAddZeroClass β] [IsAddSemigroup β] : IsAddSemigroup (AddMonoidAlgebra α β S) where
  add_assoc a b c := by ext; simp [add_assoc]

instance [AddMonoidOps β] [IsAddMonoid β] : IsAddMonoid (AddMonoidAlgebra α β S) where
  zero_nsmul a := by ext; simp
  succ_nsmul n a := by ext x; simp [succ_nsmul]

instance [AddMonoidOps β] [IsAddMonoid β] : IsAddMonoid (AddMonoidAlgebra α β S) where
  zero_nsmul a := by ext; simp
  succ_nsmul n a := by ext x; simp [succ_nsmul]

instance [Zero β] [Neg β] [IsNegZeroClass β] : IsNegZeroClass (AddMonoidAlgebra α β S) where
  neg_zero := by ext x; simp

instance [AddGroupOps β] [IsNegZeroClass β] [IsSubNegMonoid β] : IsSubNegMonoid (AddMonoidAlgebra α β S) where
  sub_eq_add_neg f g := by ext; simp [sub_eq_add_neg]
  zsmul_ofNat n f := by ext; simp [zsmul_ofNat]
  zsmul_negSucc n f := by ext; simp [zsmul_negSucc]

instance [AddGroupOps β] [IsAddGroup β] : IsAddGroup (AddMonoidAlgebra α β S) where
  neg_add_cancel a := by ext; simp [neg_add_cancel]

instance [Zero β] [Add β] [IsAddZeroClass β] [IsAddCommMagma β] : IsAddCommMagma (AddMonoidAlgebra α β S) where
  add_comm a b := by ext; apply add_comm

def mul' [Add α] [DecidableEq α] [AddMonoidOps β] [IsAddMonoid β] [IsAddCommMagma β] [Mul β] [IsMulZeroClass β]
  (f g: AddMonoidAlgebra α β S) : AddMonoidAlgebra α β S :=
    f.toFinsupp.sum
      (fun i a =>
        g.toFinsupp.sum
          (fun j b => single (i + j) (a * b))
          (by intro i₀ eq; simp [eq]))
      (by
        intro i₀ eq
        simp [eq]
        rw [Finsupp.sum_eq_zero]
        intro; rfl)

instance [Add α] [DecidableEq α] [AddMonoidOps β] [IsAddMonoid β] [IsAddCommMagma β] [Mul β] [IsMulZeroClass β] : Mul (AddMonoidAlgebra α β S) where
  mul := mul'

def mul_def [Add α] [DecidableEq α] [AddMonoidOps β] [IsAddMonoid β] [IsAddCommMagma β] [Mul β] [IsMulZeroClass β]
  (f g: AddMonoidAlgebra α β S) : f * g = mul' f g := rfl

def single_add [DecidableEq α] [Zero β] [Add β] [IsAddZeroClass β] (i: α) (a b: β) : single (S := S) i a + single i b = single i (a + b) := by
  ext x
  simp [apply_single]
  split
  rfl
  rw [add_zero]


axiom MySorry {α}: α

instance [Add α] [DecidableEq α] [AddMonoidOps β] [Mul β] [IsNonUnitalNonAssocSemiring β] :
  IsNonUnitalNonAssocSemiring (AddMonoidAlgebra α β S) where
  zero_mul := by
    intro a; ext; rw [mul_def, mul']
    have : toFinsupp 0 = (0: Finsupp α β S) := rfl
    conv => { lhs; arg 1; arg 1; rw [this] }
    rw [Finsupp.zero_sum]
  mul_zero := by
    intro a; rw [mul_def, mul']
    rw [Finsupp.sum_eq_zero]
    intro i
    apply Finsupp.zero_sum
  left_distrib := by
    intro ⟨k⟩ ⟨a⟩ ⟨b⟩
    simp [mul_def, mul', add_def]
    apply toFinsupp_inj
    simp
    conv => { rhs; rw [add_def'] }
    congr
    rw [Finsupp.add_sum']
    congr; ext a₀ b₀ a₁
    rw [Finsupp.add_sum]
    intro i b₁ b₂
    rw [mul_add, single_add]
  right_distrib := by
    intro ⟨a⟩ ⟨b⟩ ⟨k⟩
    simp [mul_def, mul', add_def]
    apply toFinsupp_inj
    simp
    conv => { rhs; rw [add_def'] }
    congr
    rw [Finsupp.add_sum]
    intro i b₁ b₂
    congr; ext i
    rw [Finsupp.add_sum']
    congr
    ext a₀ b₀ a₁
    rw [single_add, add_mul]

def sum_toFinsupp
  [FiniteSupportSet S ι]
  [Zero α] [Add α] [IsAddZeroClass α]
  [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ]
  (f: Finsupp ι α S) (g₀: ι -> α -> AddMonoidAlgebra ι γ S) {h₀ h₁} : (f.sum g₀ h₀).toFinsupp =
    f.sum (fun i a => (g₀ i a).toFinsupp) h₁ := sorry

instance [Add α] [DecidableEq α] [AddMonoidOps β] [Mul β]
  [IsNonUnitalNonAssocSemiring β] [IsSemigroup β] : IsSemigroup (AddMonoidAlgebra α β S) where
  mul_assoc := by
    intro a b c
    simp [mul_def, mul']
    classical


    rw [sum_toFinsupp]
    rw [Finsupp.sum_sum_index (f := a.toFinsupp)]
    -- simp [Multiset.sum_sum_reindex]

    -- generalize a.toFinsupp.support.val = asupp
    -- generalize b.toFinsupp.support.val = bsupp


    sorry

end AddMonoidAlgebra

/-

(Multiset.map
      (fun i =>
        (Multiset.map
            (fun i_1 =>
              single (i + i_1)
                ((Multiset.map
                          (fun i =>
                            (Multiset.map (fun i_2 => single (i + i_2) (a.toFinsupp i * b.toFinsupp i_2))
                                b.toFinsupp.support.val).sum)
                          a.toFinsupp.support.val).sum.toFinsupp
                    i *
                  c.toFinsupp i_1))
            c.toFinsupp.support.val).sum)
      (Multiset.map
                (fun i =>
                  (Multiset.map (fun i_1 => single (i + i_1) (a.toFinsupp i * b.toFinsupp i_1))
                      b.toFinsupp.support.val).sum)
                a.toFinsupp.support.val).sum.toFinsupp.support.val).sum

-/
