import Math.Data.Finset.Like
import Math.Data.Trunc
import Math.Order.Lattice.Basic
import Math.Data.Finset.Lattice
import Math.Algebra.Group.Defs
import Math.Logic.Basic

class FiniteSupportSet (S: Type*) (α: outParam Type*) extends FinsetLike S α, Sup S, Inf S, LE S, LT S, IsLattice S, Inhabited S, IsLawfulEmptyFinsetLike S where
  coe_resp_le: ∀{a b: S}, a ≤ b ↔ (a: Finset α) ≤ (b: Finset α)
  singleton: α -> S
  mem_singleton: ∀a: α, a ∈ singleton a

structure FinSupp (α β S: Type*) [Zero β] [FiniteSupportSet S α] where
  toFun: α -> β
  spec: Trunc { set : S // ∀x, toFun x ≠ 0 -> x ∈ set }

namespace FiniteSupportSet

open Classical

variable [FiniteSupportSet S α]

def coe_resp_lt {a b: S} : a < b ↔ (a: Finset α) < (b: Finset α) := by
  simp only [lt_iff_le_and_not_le, coe_resp_le]

def coe_sup_sub_sup_coe (a b: S) : (a ⊔ b: Finset α) ≤ ((a ⊔ b: S): Finset α) := by
  apply sup_le
  apply coe_resp_le.mp
  apply le_sup_left
  apply coe_resp_le.mp
  apply le_sup_right

def inf_coe_sub_coe_inf (a b: S) : ((a ⊓ b: S): Finset α) ≤ (a ⊓ b: Finset α) := by
  apply le_inf
  apply coe_resp_le.mp
  apply inf_le_left
  apply coe_resp_le.mp
  apply inf_le_right

end FiniteSupportSet

namespace FinSupp

variable [FiniteSupportSet S α]

instance [Zero β] : FunLike (FinSupp α β S) α β where
  coe f := f.toFun
  coe_inj := by
    intro a b eq; cases a ; cases b; congr
    cases eq
    exact Subsingleton.helim rfl _ _

@[ext]
def ext [Zero β] (f g: FinSupp α β S) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _

instance [Zero β] : Zero (FinSupp α β S) where
  zero := {
    toFun _ := 0
    spec := Trunc.mk {
      val := default
      property := nofun
    }
  }

@[simp] def apply_zero [Zero β] (x: α) : (0: FinSupp α β S) x = 0 := rfl

def single [Zero β] [DecidableEq α] (a: α) (b: β) : FinSupp α β S where
  toFun x := if x = a then b else 0
  spec := Trunc.mk {
    val := FiniteSupportSet.singleton a
    property x hx := by
      dsimp at hx
      split at hx
      subst x
      apply FiniteSupportSet.mem_singleton
      contradiction
  }

def apply_single [Zero β] [DecidableEq α] {a: α} {b: β} (x: α) : single (S := S) a b x = if x = a then b else 0 := rfl

instance [Zero β] [Add β] [IsAddZeroClass β] : Add (FinSupp α β S) where
  add f g := {
    toFun x := f x + g x
    spec := do
      let ⟨fs, hf⟩←f.spec
      let ⟨gs, hg⟩←g.spec
      return {
        val := fs ⊔ gs
        property x ne := by
          classical
          replace ne : f x + g x ≠ 0 := ne
          by_cases x ∈ fs
          apply FiniteSupportSet.coe_sup_sub_sup_coe
          apply Finset.mem_union.mpr
          left; assumption
          by_cases x ∈ gs
          apply FiniteSupportSet.coe_sup_sub_sup_coe
          apply Finset.mem_union.mpr
          right; assumption
          rename_i fx gx
          have fx_eq_zero : f x = 0 := Classical.not_not.mp (Classical.contrapositive.mpr (hf x) fx)
          have gx_eq_zero : g x = 0 := Classical.not_not.mp (Classical.contrapositive.mpr (hg x) gx)
          rw [fx_eq_zero, gx_eq_zero, add_zero] at ne
          contradiction
      }
  }

instance [Zero β] [Neg β] [IsNegZeroClass β] : Neg (FinSupp α β S) where
  neg f := {
    toFun x := -f x
    spec := do
      let ⟨fs, hf⟩←f.spec
      return {
        val := fs
        property x ne := by
          classical
          replace ne : -f x ≠ 0 := ne
          by_cases f x = 0 <;> rename_i h
          rw [h, neg_zero] at ne
          contradiction
          apply hf
          assumption
      }
  }

instance [AddMonoidOps β] [IsAddMonoid β] : SMul ℕ (FinSupp α β S) where
  smul n f := {
    toFun x := n • f x
    spec := do
      let ⟨fs, hf⟩←f.spec
      return {
        val := fs
        property x ne := by
          classical
          replace ne : n • f x ≠ 0 := ne
          by_cases f x = 0 <;> rename_i h
          rw [h, nsmul_zero (α := β) (a := n)] at ne
          contradiction
          apply hf
          assumption
      }
  }

instance [AddGroupOps β] [IsNegZeroClass β] [IsSubNegMonoid β] : Sub (FinSupp α β S) where
  sub f g := {
    toFun x := f x - g x
    spec := do
      let ⟨fs, hf⟩←f.spec
      let ⟨gs, hg⟩←g.spec
      return {
        val := fs ⊔ gs
        property x ne := by
          classical
          replace ne : f x - g x ≠ 0 := ne
          by_cases x ∈ fs
          apply FiniteSupportSet.coe_sup_sub_sup_coe
          apply Finset.mem_union.mpr
          left; assumption
          by_cases x ∈ gs
          apply FiniteSupportSet.coe_sup_sub_sup_coe
          apply Finset.mem_union.mpr
          right; assumption
          rename_i fx gx
          have fx_eq_zero : f x = 0 := Classical.not_not.mp (Classical.contrapositive.mpr (hf x) fx)
          have gx_eq_zero : g x = 0 := Classical.not_not.mp (Classical.contrapositive.mpr (hg x) gx)
          rw [fx_eq_zero, gx_eq_zero, sub_zero] at ne
          contradiction
      }
  }

instance [AddGroupOps β] [IsNegZeroClass β] [IsSubNegMonoid β] : SMul ℤ (FinSupp α β S) where
  smul n f := {
    toFun x := n • f x
    spec := do
      let ⟨fs, hf⟩←f.spec
      return {
        val := fs
        property x ne := by
          classical
          replace ne : n • f x ≠ 0 := ne
          by_cases f x = 0 <;> rename_i h
          rw [h, zsmul_zero (α := β) (a := n)] at ne
          contradiction
          apply hf
          assumption
      }
  }

@[simp] def apply_add [Zero β] [Add β] [IsAddZeroClass β] (f g: FinSupp α β S) (x: α) : (f + g) x = f x + g x := rfl

@[simp] def apply_neg [Zero β] [Neg β] [IsNegZeroClass β] (f: FinSupp α β S) (x: α) : (-f) x = -f x := rfl

@[simp] def apply_nsmul [AddMonoidOps β] [IsAddMonoid β] (n: ℕ) (f: FinSupp α β S) (x: α) : (n • f) x = n • f x := rfl

@[simp] def apply_sub [AddGroupOps β] [IsNegZeroClass β] [IsSubNegMonoid β] (f g: FinSupp α β S) (x: α) : (f - g) x = f x - g x := rfl

@[simp] def apply_zsmul [AddGroupOps β] [IsNegZeroClass β] [IsSubNegMonoid β] (n: ℤ) (f: FinSupp α β S) (x: α) : (n • f) x = n • f x := rfl

instance [Zero β] [Add β] [IsAddZeroClass β] : IsAddZeroClass (FinSupp α β S) where
  zero_add _ := by ext; simp
  add_zero _ := by ext; simp

instance [Zero β] [Add β] [IsAddZeroClass β] [IsAddSemigroup β] : IsAddSemigroup (FinSupp α β S) where
  add_assoc a b c := by ext; simp [add_assoc]

instance [AddMonoidOps β] [IsAddMonoid β] : IsAddMonoid (FinSupp α β S) where
  zero_nsmul a := by ext; simp
  succ_nsmul n a := by ext x; simp [succ_nsmul]

instance [AddMonoidOps β] [IsAddMonoid β] : IsAddMonoid (FinSupp α β S) where
  zero_nsmul a := by ext; simp
  succ_nsmul n a := by ext x; simp [succ_nsmul]

instance [Zero β] [Neg β] [IsNegZeroClass β] : IsNegZeroClass (FinSupp α β S) where
  neg_zero := by ext x; simp

instance [AddGroupOps β] [IsNegZeroClass β] [IsSubNegMonoid β] : IsSubNegMonoid (FinSupp α β S) where
  sub_eq_add_neg f g := by ext; simp [sub_eq_add_neg]
  zsmul_ofNat n f := by ext; simp [zsmul_ofNat]
  zsmul_negSucc n f := by ext; simp [zsmul_negSucc]

instance [AddGroupOps β] [IsAddGroup β] : IsAddGroup (FinSupp α β S) where
  neg_add_cancel a := by ext; simp [neg_add_cancel]

end FinSupp
