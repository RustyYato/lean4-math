import Math.Data.DFinsupp.Support
import Math.Algebra.Group.Hom
import Math.Algebra.Module.Defs
import Math.Data.Trunc

open scoped LazyFinset

structure DFinsupp (α: ι -> Type*) (S: Type*) [FiniteSupportOps S ι] [∀i, Zero (α i)] where
  toFun (i: ι): α i
  spec: Trunc { set : S // ∀(i: ι), toFun i ≠ 0 -> i ∈ set }

namespace DFinsupp

variable {α: ι -> Type*}

section Basics

variable [∀i, Zero (α i)] [FiniteSupportOps S ι] [DecidableEq ι]

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

def single [DecidableEq ι] [∀i, Zero (α i)] (i: ι) (a: α i) : DFinsupp α S where
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
def apply_single [DecidableEq ι] [∀i, Zero (α i)] (i j: ι) (a: α i) : single (S := S) i a j = if h:i = j then cast (by rw [h]) a else 0 := rfl

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

instance (priority := 900) [∀i, SMul R (α i)] [∀i, Zero (α i)] [∀i, IsSMulZeroClass R (α i)] : SMul R (DFinsupp α S) where
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
-- @[simp] def apply_mul [∀i, Zero (α i)] [∀i, Mul (α i)] [∀i, IsMulZeroClass (α i)] (f g: DFinsupp α S) (i: ι) : (f * g) i = f i * g i := rfl
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

-- instance [∀i, Zero (α i)] [∀i, Mul (α i)] [∀i, IsMulZeroClass (α i)] [∀i, IsCommMagma (α i)]
--   : IsCommMagma (DFinsupp α S) where
--   mul_comm _ _ := by ext; apply mul_comm

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

def erase [DecidableEq ι] [∀i, Zero (α i)] (a: ι) (f: DFinsupp α S) : DFinsupp α S where
  toFun x := if x = a then 0 else f x
  spec := do
    let ⟨fs, hf⟩←f.spec
    return {
      val := FiniteSupport.remove a fs
      property x ne := by
        split at ne
        contradiction
        have := hf x ne
        apply FiniteSupport.mem_remove
        assumption
        symm; assumption
    }

def apply_erase [DecidableEq ι] [∀i, Zero (α i)] (f: DFinsupp α S) (a x: ι) :
  f.erase a x = if x = a then 0 else f x := rfl

variable [∀i, Zero (α i)] [dec: ∀i (x: α i), Decidable (x = 0)]

def support (f: DFinsupp α S) : LazyFinset ι :=
  f.spec.lift (fun s => (s.val: LazyFinset ι).filter fun x => decide (f x ≠ 0)) <| by
    intro ⟨a, ha⟩ ⟨b, hb⟩
    dsimp
    ext x
    simp [Finset.mem_filter]
    intro h
    apply Iff.intro <;> intro
    apply hb; assumption
    apply ha; assumption

def mem_support {f: DFinsupp α S} :
  ∀{x}, x ∈ f.support ↔ f x ≠ 0 := by
  intro x
  cases f with | mk f h =>
  induction h with | mk h =>
  obtain ⟨s, h⟩ := h
  unfold support
  show x ∈ LazyFinset.filter (fun x => f x ≠ 0) s ↔ f x ≠ 0
  simp
  apply h

def eq_support_union [∀i, Zero (α i)] [∀i (x: α i), Decidable (x = 0)] (f: DFinsupp α S)
  (supp: LazyFinset ι) (supp_spec: ∀ (x : ι), f x ≠ 0 → x ∈ supp) :
  ∃rest,  (∀x ∈ f.support, ¬x ∈ rest) ∧ supp = f.support ++ rest := by
  classical
  refine ⟨supp \ f.support, ?_, ?_⟩
  intro x h g
  rw [LazyFinset.mem_sdiff] at g
  exact g.right h
  ext x
  simp [Finset.mem_sdiff, Finset.mem_union_disjoint]
  apply Iff.intro
  intro h
  simp [h]
  apply Classical.em
  intro h
  rcases h with h | ⟨h, h₀⟩
  apply supp_spec
  apply mem_support.mp
  assumption
  assumption

def support_single [DecidableEq ι] : (single a b: DFinsupp α S).support ⊆ {a} := by
 intro i h
 rw [LazyFinset.mem_singleton]
 rw [mem_support] at h
 unfold single at h
 rw [←toFun_eq_coe] at h
 simp at h
 obtain ⟨rfl, h⟩ := h
 rfl

def support_add [∀i, Add (α i)] [∀i, IsAddZeroClass (α i)] [DecidableEq ι] (f g: DFinsupp α S) :
  (f + g).support ⊆ f.support ∪ g.support := by
  intro i
  simp [mem_support, Finset.mem_union]
  rw [←Classical.not_and_iff_not_or_not, Classical.contrapositive]
  intro ⟨ha, hb⟩
  rw [ha, hb, add_zero]

def support_zero [Zero β] [∀b: β, Decidable (b = 0)] : support (S := S) (α := α) 0 = ∅ := by
  ext
  simp [mem_support]

def support_erase [DecidableEq ι] [∀i, DecidableEq (α i)] (f: DFinsupp α S) : (f.erase x).support = f.support.erase x := by
  ext a
  simp [mem_support, Finset.mem_erase, apply_erase]
  rw [And.comm]

def support_smul [∀i, Zero (α i)] [∀i, SMul R (α i)] [∀i, IsSMulZeroClass R (α i)] [∀i (a: α i), Decidable (a = 0)] [DecidableEq ι] (x: R) (f: DFinsupp α S) :
  (x • f).support ⊆ f.support := by
  intro i
  simp [mem_support, Finset.mem_union]
  intro h g; apply h
  show x • f i = 0
  rw [g, smul_zero]

end Algebra

end DFinsupp
