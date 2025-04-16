import Math.Data.Finsupp.Basic
import Math.Data.Finsupp.Algebra
import Math.Algebra.Module.Defs
import Math.AxiomBlame

structure AddMonoidAlgebra (α β S: Type*) [Zero β] [FiniteSupportOps S α] where
  ofFinsupp ::
  toFinsupp : Finsupp α β S

namespace AddMonoidAlgebra

variable [FiniteSupportOps S α] [Zero β]

instance : FunLike (AddMonoidAlgebra α β S) α β where
  coe f := f.toFinsupp
  coe_inj := by
    intro a b eq; cases a ; cases b; congr
    apply DFunLike.coe_inj
    assumption

@[ext]
def ext (f g: AddMonoidAlgebra α β S) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _

instance : Zero (AddMonoidAlgebra α β S) where
  zero := ⟨0⟩

@[simp] def apply_zero (x: α) : (0: AddMonoidAlgebra α β S) x = 0 := rfl

def toFinsupp_inj : Function.Injective (toFinsupp (α := α) (β := β) (S := S)) := by
  intro a b eq; cases a; congr

instance [DecidableEq β] : DecidableEq (AddMonoidAlgebra α β S) :=
  fun a b => decidable_of_iff (a.toFinsupp = b.toFinsupp) toFinsupp_inj.eq_iff

end AddMonoidAlgebra

namespace AddMonoidAlgebra

variable [FiniteSupport S α]

def single [Zero β] [DecidableEq α] (a: α) (b: β) : AddMonoidAlgebra α β S where
  toFinsupp := .single a b

def apply_single {β} [Zero β] [DecidableEq α] {a: α} {b: β} (x: α) : single (S := S) a b x = if x = a then b else 0 := rfl

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

instance [Zero β] [Mul β] [IsMulZeroClass β] : SMul β (AddMonoidAlgebra α β S) where
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
  mul_add := by
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
  add_mul := by
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
  [FiniteSupport S ι]
  [Zero α] [Add α] [IsAddZeroClass α]
  [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ]
  (f: Finsupp ι α S) (g₀: ι -> α -> AddMonoidAlgebra ι γ S) {h₀ h₁} :
  (f.sum g₀ h₀).toFinsupp = f.sum (fun i a => (g₀ i a).toFinsupp) h₁ := by
  let f' : AddGroupHom (AddMonoidAlgebra ι γ S) (Finsupp ι γ S) := {
    toFun := toFinsupp
    map_zero := rfl
    map_add := rfl
  }
  show f' (f.sum g₀ h₀) = _
  rw [Finsupp.map_sum]
  rfl

def sum_toFinsupp'
  [FiniteSupport S ι]
  [Zero α] [Add α] [IsAddZeroClass α]
  [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ]
  (f: Finsupp ι α S) (g₀: ι -> α -> AddMonoidAlgebra ι γ S) {h₀} :
  (f.sum g₀ h₀).toFinsupp i₀ = f.sum (fun i a => (g₀ i a).toFinsupp i₀) (by
    intro i h
    simp
    rw [h₀ _ h]
    rfl) := by
  let f' : (AddMonoidAlgebra ι γ S) →+ γ := {
    toFun x := x.toFinsupp i₀
    map_zero := rfl
    map_add := rfl
  }
  show f' (f.sum g₀ h₀) = _
  rw [Finsupp.map_sum]
  congr

@[simp]
def single_toFinsupp
  [FiniteSupport S ι] [Zero α] [DecidableEq ι] :
  (single a b: AddMonoidAlgebra ι α S).toFinsupp  = Finsupp.single a b := rfl

def single_mul [Add α] [DecidableEq α] [AddMonoidOps β] [IsAddMonoid β] [IsAddCommMagma β] [Mul β] [IsMulZeroClass β]
  (a₀ a₁: α) (b₀ b₁: β) : single (S := S) a₀ b₀ * single a₁ b₁ = single (a₀ + a₁) (b₀ * b₁) := by
  rw [mul_def, mul']
  conv => { lhs; arg 1; rw [single_toFinsupp] }
  rw [Finsupp.single_sum]
  conv => { lhs; arg 1; rw [single_toFinsupp] }
  rw [Finsupp.single_sum]

def single_inj [Zero β] [DecidableEq α] : Function.Injective (single (S := S) (β := β) a) := by
  intro x y eq
  have : (single (S := S) a x).toFinsupp a = (single (S := S) a y).toFinsupp a := by rw [eq]
  rw [single_toFinsupp, single_toFinsupp, Finsupp.apply_single, Finsupp.apply_single] at this
  rw [if_pos rfl, if_pos rfl] at this
  assumption

instance [Add α] [IsAddSemigroup α] [DecidableEq α] [AddMonoidOps β] [Mul β]
  [IsNonUnitalNonAssocSemiring β] [IsSemigroup β] : IsSemigroup (AddMonoidAlgebra α β S) where
  mul_assoc := by
    intro a b c
    simp [mul_def, mul']
    classical
    conv => {
      lhs; arg 1
      rw [sum_toFinsupp a.toFinsupp (h₁ := by
        intro i h
        rw [h]
        dsimp
        rw [Finsupp.sum_eq_zero]; rfl
        intro i₀
        rw [zero_mul, single_zero])]
    }
    rw [Finsupp.sum_sum_index]
    conv => {
      lhs; arg 2; intro a b
      rw [sum_toFinsupp (h₁ := by
        intro i h
        rw [h]
        dsimp
        rw [mul_zero, single_zero]; rfl)]
    }
    conv => {
      rhs
      arg 2; intro a b
      arg 1
      rw [sum_toFinsupp (h₁ := by
        intro i eq; rw [eq]
        dsimp; rw [Finsupp.sum_eq_zero]; rfl
        intro i₀; rw [zero_mul, single_zero])]
    }
    congr 1
    ext a₀ b₀ a₁
    rw [Finsupp.sum_sum_index]
    conv => {
      lhs; lhs; lhs; intro a b; rw [single]
    }
    rw [Finsupp.sum_sum_index]
    congr
    ext a₂ b₁ a₃
    simp
    rw [Finsupp.single_sum,
      sum_toFinsupp,
      Finsupp.sum_sum_index]
    simp [Finsupp.single_sum]
    congr
    ext _ _
    rw [add_assoc, mul_assoc]
    intro i a b; simp [single_add, single_mul, mul_add]
    intro i; simp; rfl
    intro; simp
    intro i a b; simp [single_add, single_mul, mul_add]
    intro i; simp; rw [Finsupp.sum_eq_zero]; rfl
    intros; rfl
    intros; simp
    · intro i a b
      rw [Finsupp.sum_pairwise]
      congr
      ext i b
      simp [single_add, single_mul, add_mul]
    intros; simp; rfl
    intro i; simp; rw [Finsupp.sum_eq_zero]
    intros; rfl
    · intro i a b
      rw [Finsupp.sum_pairwise]
      congr
      ext i b
      simp [single_add, single_mul, add_mul]
    intros; rw [Finsupp.sum_eq_zero]; rfl
    intros; simp
    intros; simp; rw [Finsupp.sum_eq_zero]
    intros; rfl

instance [Add α] [IsAddCommMagma α] [DecidableEq α] [AddMonoidOps β] [Mul β] [IsNonUnitalNonAssocSemiring β] [IsCommMagma β] : IsCommMagma (AddMonoidAlgebra α β S) where
  mul_comm a b := by
    rw [mul_def, mul_def]; unfold mul'
    classical
    simp [Finsupp.sum_eq_support_sum]
    rw [Multiset.sum_comm]
    congr; ext a₀ a₁
    congr; ext a₂ a₃
    rw [mul_comm, add_comm]

def erase [Zero β] [DecidableEq α] (f: AddMonoidAlgebra α β S) (a: α) : AddMonoidAlgebra α β S where
  toFinsupp := f.toFinsupp.erase a

abbrev applyHom [Add β] [Zero β] [IsAddZeroClass β] (a: α) :  AddMonoidAlgebra α β S →+ β where
  toFun f := f a
  map_zero := rfl
  map_add := rfl

def applyHom_eq [Add β] [Zero β] [IsAddZeroClass β] (f: AddMonoidAlgebra α β S) (a: α) : applyHom a f = f.toFinsupp a := rfl

instance [SemiringOps β] [IsSemiring β] : IsModule β (AddMonoidAlgebra α β S) where
  one_smul a := by
    ext i
    apply one_mul
  mul_smul a b c := by
    ext i
    apply mul_assoc
  smul_zero a := by
    ext i
    apply mul_zero
  smul_add a b c := by
    ext i
    apply mul_add
  add_smul a b c := by
    ext i
    apply add_mul
  zero_smul a := by
    ext i
    apply zero_mul

def induction
  [DecidableEq α] [AddMonoidOps β] [IsAddMonoid β]
  {motive: AddMonoidAlgebra α β S -> Prop}
  (zero: motive 0)
  (single_add: ∀a b c, b ≠ 0 -> motive c -> motive (single a b + c))
  (x: AddMonoidAlgebra α β S) : motive x := by
  obtain ⟨f, spec⟩ := x
  induction spec with | mk spec =>
  obtain ⟨degree', spec'⟩ := spec
  replace ⟨degree, spec⟩: Σ' s: Finset α, ∀x, f x ≠ 0 -> x ∈ s := ⟨degree', spec'⟩
  induction degree with
  | mk degree nodup =>
  replace spec:  ∀x, f x ≠ 0 -> x ∈ degree := spec
  clear nodup
  induction degree generalizing f with
  | nil =>
    rw [show ofFinsupp (.mk f _) = 0 from ?_]
    apply zero
    ext a; show f a = 0
    apply Classical.byContradiction
    intro h
    have := spec _ h
    contradiction
  | cons a as ih =>
    -- replace ih := ih
    rw [show ofFinsupp (.mk f _) =
        .single a (f a) + .ofFinsupp (.mk (
          fun x => if x = a then 0 else f x
        ) (Trunc.mk ⟨degree', (by
          intro x hx
          simp at hx
          apply spec'
          exact hx.right)⟩))
      from ?_]
    by_cases ha:f a = 0
    · rw [ha]; simp
      apply ih
      simp; intros x ne hx
      have := spec x hx; simp at this
      apply this.resolve_left
      assumption
    · apply single_add
      assumption
      apply ih
      simp; intros x ne hx
      have := spec x hx; simp at this
      apply this.resolve_left
      assumption
    ext x
    show f x = AddMonoidAlgebra.single  a (f a) x + (if x = a then 0 else f x)
    rw [AddMonoidAlgebra.apply_single]
    split <;> simp
    subst a; rfl

end AddMonoidAlgebra
