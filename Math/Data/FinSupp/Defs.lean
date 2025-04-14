import Math.Data.Finset.Like
import Math.Data.Trunc
import Math.Order.Lattice.Basic
import Math.Data.Finset.Lattice
import Math.Algebra.Group.Hom
import Math.Logic.Basic
import Math.Algebra.Module.Defs

class FiniteSupportSet (S: Type*) (α: outParam Type*) extends FinsetLike S α, Max S, Min S, LE S, LT S, IsLattice S, Inhabited S, IsLawfulEmptyFinsetLike S where
  coe_map_le: ∀{a b: S}, a ≤ b ↔ (a: Finset α) ≤ (b: Finset α)
  singleton: α -> S
  mem_singleton: ∀a: α, a ∈ singleton a
  remove: α -> S -> S
  mem_remove: ∀(s: S) (x a: α), x ∈ s -> a ≠ x -> x ∈ remove a s

structure Finsupp (α β S: Type*) [Zero β] [FiniteSupportSet S α] where
  toFun: α -> β
  spec: Trunc { set : S // ∀x, toFun x ≠ 0 -> x ∈ set }

namespace FiniteSupportSet

variable [FiniteSupportSet S α] [DecidableEq α]

def coe_map_lt {a b: S} : a < b ↔ (a: Finset α) < (b: Finset α) := by
  simp only [lt_iff_le_and_not_le, coe_map_le]

def coe_max_sub_max_coe (a b: S) : (a ⊔ b: Finset α) ≤ ((a ⊔ b: S): Finset α) := by
  apply max_le
  apply coe_map_le.mp
  apply le_max_left
  apply coe_map_le.mp
  apply le_max_right

def min_coe_sub_coe_min (a b: S) : ((a ⊓ b: S): Finset α) ≤ (a ⊓ b: Finset α) := by
  apply le_min
  apply coe_map_le.mp
  apply min_le_left
  apply coe_map_le.mp
  apply min_le_right

end FiniteSupportSet

instance [DecidableEq α] : FiniteSupportSet (Finset α) α where
  coe_map_le := Iff.rfl
  singleton a := {a}
  mem_singleton _ := Finset.mem_singleton.mpr rfl
  remove a s := s.erase a
  mem_remove _ _ _ h g := Finset.mem_erase.mpr ⟨h, g.symm⟩

instance : FiniteSupportSet Nat Nat where
  coe_map_le {a b} := by
    conv => {
      rhs; rw [LE.le, Finset.instLE]
    }
    dsimp [HasSubset.Subset]
    conv => {
      rhs; intro x
      erw [Nat.mem_iff_lt, Nat.mem_iff_lt]
    }
    apply Iff.intro
    intro h x hx
    apply Nat.lt_of_lt_of_le
    assumption
    assumption
    intro h
    rcases Nat.lt_or_ge b a with g | g
    have := Nat.lt_irrefl _ (h _ g)
    contradiction
    assumption
  singleton a := a+1
  mem_singleton _ := (Nat.mem_iff_lt _ _).mpr (Nat.lt_succ_self _)
  remove a s := s
  mem_remove _ _ _ h _ := h

namespace Finsupp

variable [FiniteSupportSet S α]

instance [Zero β] : FunLike (Finsupp α β S) α β where
  coe f := f.toFun
  coe_inj := by
    intro a b eq; cases a ; cases b; congr
    cases eq
    exact Subsingleton.helim rfl _ _

@[ext]
def ext [Zero β] (f g: Finsupp α β S) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _

instance [Zero β] : Zero (Finsupp α β S) where
  zero := {
    toFun _ := 0
    spec := Trunc.mk {
      val := default
      property := nofun
    }
  }

@[simp] def apply_zero [Zero β] (x: α) : (0: Finsupp α β S) x = 0 := rfl

def single [Zero β] [DecidableEq α] (a: α) (b: β) : Finsupp α β S where
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

instance [Zero β] [Add β] [IsAddZeroClass β] : Add (Finsupp α β S) where
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
          apply FiniteSupportSet.coe_max_sub_max_coe
          apply Finset.mem_union.mpr
          left; assumption
          by_cases x ∈ gs
          apply FiniteSupportSet.coe_max_sub_max_coe
          apply Finset.mem_union.mpr
          right; assumption
          rename_i fx gx
          have fx_eq_zero : f x = 0 := Classical.not_not.mp (Classical.contrapositive.mpr (hf x) fx)
          have gx_eq_zero : g x = 0 := Classical.not_not.mp (Classical.contrapositive.mpr (hg x) gx)
          rw [fx_eq_zero, gx_eq_zero, add_zero] at ne
          contradiction
      }
  }

instance [Zero β] [Neg β] [IsNegZeroClass β] : Neg (Finsupp α β S) where
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

instance [AddMonoidOps β] [IsAddMonoid β] : SMul ℕ (Finsupp α β S) where
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

instance [AddGroupOps β] [IsNegZeroClass β] [IsSubNegMonoid β] : Sub (Finsupp α β S) where
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
          apply FiniteSupportSet.coe_max_sub_max_coe
          apply Finset.mem_union.mpr
          left; assumption
          by_cases x ∈ gs
          apply FiniteSupportSet.coe_max_sub_max_coe
          apply Finset.mem_union.mpr
          right; assumption
          rename_i fx gx
          have fx_eq_zero : f x = 0 := Classical.not_not.mp (Classical.contrapositive.mpr (hf x) fx)
          have gx_eq_zero : g x = 0 := Classical.not_not.mp (Classical.contrapositive.mpr (hg x) gx)
          rw [fx_eq_zero, gx_eq_zero, sub_zero] at ne
          contradiction
      }
  }

instance [AddGroupOps β] [IsNegZeroClass β] [IsSubNegMonoid β] : SMul ℤ (Finsupp α β S) where
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

instance [Zero β] [Mul β] [IsMulZeroClass β] : SMul β (Finsupp α β S) where
  smul n f := {
    toFun x := n * f x
    spec := do
      let ⟨fs, hf⟩←f.spec
      return {
        val := fs
        property x ne := by
          classical
          replace ne : n * f x ≠ 0 := ne
          by_cases f x = 0 <;> rename_i h
          rw [h, mul_zero] at ne
          contradiction
          apply hf
          assumption
      }
  }

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

instance [Zero β] [Add β] [IsAddZeroClass β] [IsAddCommMagma β] : IsAddCommMagma (Finsupp α β S) where
  add_comm a b := by ext; apply add_comm

instance [SemiringOps β] [IsSemiring β] : IsModule β (Finsupp α β S) where
  one_smul f := by
    ext x
    apply one_mul
  mul_smul a b f := by
    ext
    apply mul_assoc
  smul_add r a b := by
    ext
    apply mul_add
  zero_smul f := by
    ext
    apply zero_mul
  smul_zero b := by
    ext
    apply mul_zero
  add_smul r s b := by
    ext
    apply add_mul

def update [DecidableEq α] [Zero β] (a: α) (b: β) (f: Finsupp α β S) : Finsupp α β S where
  toFun x := if x = a then b else f x
  spec := do
    let ⟨fs, hf⟩←f.spec
    return {
      val := FiniteSupportSet.singleton a ⊔ fs
      property x ne := by
        apply FiniteSupportSet.coe_max_sub_max_coe
        apply Finset.mem_union.mpr
        split at ne
        subst x
        left; apply FiniteSupportSet.mem_singleton
        right
        apply hf
        assumption
    }

def erase [DecidableEq α] [Zero β] (a: α) (f: Finsupp α β S) : Finsupp α β S where
  toFun x := if x = a then 0 else f x
  spec := do
    let ⟨fs, hf⟩←f.spec
    return {
      val := FiniteSupportSet.remove a fs
      property x ne := by
        split at ne
        contradiction
        have := hf x ne
        apply FiniteSupportSet.mem_remove
        assumption
        symm; assumption
    }

def apply_erase [Zero β] [DecidableEq α] (f: Finsupp α β S) (a x: α) :
  f.erase a x = if x = a then 0 else f x := rfl

def singleHom [DecidableEq α] [Zero β] [Add β] [IsAddZeroClass β] (a: α) : β →+ Finsupp α β S where
  toFun := single a
  map_zero := by ext; simp [apply_single]
  map_add {f g} := by ext; simp only [apply_single, apply_add]; split <;> simp

def applyHom [Zero β] [Add β] [IsAddZeroClass β] (a: α) : Finsupp α β S →+ β where
  toFun f := f a
  map_zero := rfl
  map_add := rfl

def on [Zero β] (s: S) [DecidablePred (· ∈ s)] (f: α -> β): Finsupp α β S where
  toFun x := if x ∈ s then f x else 0
  spec := Trunc.mk {
    val := s
    property := by
      intro x h
      dsimp at h
      split at h
      assumption
      contradiction
  }

@[simp] def apply_on [Zero β] (s: S) [DecidablePred (· ∈ s)] (f: α -> β) (x: α) :
  on s f x = if x ∈ s then f x else 0 := rfl

def support [Zero β] [dec: ∀x: β, Decidable (x = 0)] (f: Finsupp α β S) : Finset α :=
  f.spec.lift (fun s => (s.val: Finset α).filter fun x => decide (f x ≠ 0)) <| by
    intro ⟨a, ha⟩ ⟨b, hb⟩
    dsimp
    ext x
    simp [Finset.mem_filter]
    intro h
    apply Iff.intro <;> intro
    apply hb; assumption
    apply ha; assumption

def mem_support [Zero β] [dec: ∀x: β, Decidable (x = 0)] {f: Finsupp α β S} :
  ∀{x}, x ∈ f.support ↔ f x ≠ 0 := by
  intro x
  cases f with | mk f h =>
  induction h with | mk h =>
  obtain ⟨s, h⟩ := h
  unfold support
  show x ∈ Finset.filter (fun x => f x ≠ 0) s ↔ f x ≠ 0
  simp [Finset.mem_filter]
  apply h

def support_on_subset [Zero β] (s: S) [DecidablePred (· ∈ s)] [dec: ∀x: β, Decidable (x = 0)] (f: α -> β) :
  support (on s f) ⊆ s := by
  intro x
  simp [mem_support]
  intros; assumption

def support_on [Zero β] (s: S) [DecidablePred (· ∈ s)] [dec: ∀x: β, Decidable (x = 0)] (f: α -> β) :
  support (on s f) = (s: Finset α).filter (fun x => f x ≠ 0) := by
  ext x
  simp [mem_support, Finset.mem_filter]

def mapRange [Zero β] [Zero γ] [FunLike F β γ] [IsZeroHom F β γ] (g: F) (f: Finsupp α β S): Finsupp α γ S where
  toFun x  := g (f x)
  spec := f.spec.map fun ⟨s, h⟩ => {
    val := s
    property := by
      intro x hx
      dsimp at hx
      by_cases hf:f x = 0
      rw [hf, map_zero] at hx
      contradiction
      apply h
      assumption
  }

@[simp] def apply_mapRange [Zero β] [Zero γ] [FunLike F β γ] [IsZeroHom F β γ] (g: F) (f: Finsupp α β S) (x: α) : mapRange g f x = g (f x) := rfl

def mapRange_zero [Zero β] [Zero γ] [FunLike F β γ] [IsZeroHom F β γ] (g: F) :
  mapRange g (0: Finsupp α β S) = 0 := by
  ext x; simp [map_zero]

def toFinset [DecidableEq α] [Zero β] (f: Finsupp α β S) : Finsupp α β (Finset α) where
  toFun := f
  spec := f.spec.map fun ⟨s, h⟩ => {
    val := s
    property := h
  }

@[simp] def toFinset_coe_eq [DecidableEq α] [Zero β] (f: Finsupp α β S) : (f.toFinset: α -> β) = f := rfl

def eq_support_union [Zero β] [∀b: β, Decidable (b = 0)] (f: Finsupp α β S)
  (supp: Finset α) (supp_spec: ∀ (x : α), f x ≠ 0 → x ∈ supp) :
  ∃rest, ∃h, supp = f.support.union_disjoint rest h := by
  classical
  refine ⟨supp \ f.support, ?_, ?_⟩
  intro x h g
  rw [Finset.mem_sdiff] at g
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

def support_single [DecidableEq α] [Zero β] [∀b: β, Decidable (b = 0)] :
 (single a b: Finsupp α β S).support ⊆ {a} := by
 intro i h
 rw [Finset.mem_singleton,]
 rw [mem_support] at h
 unfold single at h
 replace h : (if i = a then b else 0) ≠ (0: β) := h
 split at h
 assumption
 contradiction

def smul_single [Zero β] [Mul β] [IsMulZeroClass β] [∀b: β, Decidable (b = 0)] [DecidableEq α] (x b: β) (a: α) :
  x • Finsupp.single a b = Finsupp.single (S := S) a (x * b) := by
  ext i
  show x * single a b i = _
  rw [Finsupp.apply_single, Finsupp.apply_single]
  split; rfl
  rw [mul_zero]

def support_smul [Zero β] [Mul β] [IsMulZeroClass β] [∀b: β, Decidable (b = 0)] [DecidableEq α] (x: β) (f: Finsupp α β S) :
  (x • f).support ⊆ f.support := by
  intro i
  simp [mem_support, Finset.mem_union]
  intro h g; apply h
  show x * f i = 0
  rw [g, mul_zero]

def support_add [Zero β] [Add β] [IsAddZeroClass β] [∀b: β, Decidable (b = 0)] [DecidableEq α] (f g: Finsupp α β S) :
  (f + g).support ⊆ f.support ∪ g.support := by
  intro i
  simp [mem_support, Finset.mem_union]
  rw [←Classical.not_and_iff_not_or_not, Classical.contrapositive]
  intro ⟨ha, hb⟩
  rw [ha, hb, add_zero]

def support_zero [Zero β] [∀b: β, Decidable (b = 0)] : support (S := S) (β := β) 0 = ∅ := by
  ext
  simp [mem_support]
  apply Finset.not_mem_empty

def support_erase [Zero β] [DecidableEq α] [DecidableEq β] (f: Finsupp α β S) : (f.erase x).support = f.support.erase x := by
  ext a
  simp [mem_support, Finset.mem_erase, apply_erase]
  rw [And.comm]

def induction [Zero β] [Add β] [IsAddZeroClass β] [DecidableEq α]
  {motive: Finsupp α β S -> Prop}
  (zero: motive 0)
  (single: ∀a b, motive (single a b))
  (add: ∀a b,
    motive a ->
    motive b ->
    (∀x, a x + b x = 0 -> a x = 0 ∧ b x = 0) ->
    (Set.support a ∩ Set.support b = ∅) ->
    motive (a + b)):
  ∀f, motive f := by
  intro f
  classical
  cases h:f.support with
  | mk supp suppnodup =>
  replace h : f.support.val = supp := by rw [h]
  clear suppnodup
  induction supp generalizing f with
  | nil =>
    rw [show f = 0 from ?_]
    assumption
    ext x
    apply Classical.byContradiction
    intro g
    have : x ∈ f.support.val := mem_support.mpr g
    rw [h] at this
    contradiction
  | cons a as ih =>
    obtain ⟨supp'⟩ := f.spec
    rw [show f = Finsupp.single a (f a) + f.erase a from ?_]
    apply add
    apply single
    apply ih
    · simp [support_erase f, Finset.erase, h]
      rw [Multiset.erase_cons_head]
    · intro x h
      simp [apply_erase, apply_single] at h
      simp only [apply_erase, apply_single]
      split at h
      subst x; simp at h
      rw [if_pos rfl, if_pos rfl]
      trivial
      rename_i g
      rw [if_neg g, if_neg g]
      simp at h
      trivial
    · apply Set.ext_empty
      intro x hx
      simp [Set.mem_support, Set.mem_inter] at hx
      rw [apply_erase, apply_single] at hx
      split at hx
      exact hx.right rfl
      exact hx.left rfl
    · ext x
      simp [apply_erase, apply_single]
      split
      subst a; rw [add_zero]
      simp

end Finsupp
