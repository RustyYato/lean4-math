import Math.Data.Fintype.Basic
import Math.Data.Multiset.Algebra
import Init.Notation

variable [Fintype ι] [Fintype ι₀] [Fintype ι₁]

def sum [Zero α] [Add α] [IsAddSemigroup α] [IsAddCommMagma α] (f: ι -> α) : α := ((Finset.univ ι).val.map f).sum
def prod [One α] [Mul α] [IsSemigroup α] [IsCommMagma α] (f: ι -> α) : α := sum (α := AddOfMul α) f

section Syntax

open Lean
open TSyntax.Compat

macro "∑ " xs:explicitBinders ", " b:term:60 : term => expandExplicitBinders ``sum xs b
macro "∏ " xs:explicitBinders ", " b:term:60 : term => expandExplicitBinders ``prod xs b

end Syntax

def sum_eq_zero [AddMonoidOps α] [IsAddCommMagma α] [IsAddMonoid α] (f: ι -> α) (h: ∀i, f i = 0) : ∑i, f i = 0 := by
  apply Multiset.sum_eq_zero
  intro i
  rw [Multiset.mem_map]
  rintro ⟨_, _, rfl⟩
  apply h

def prod_eq_one [MonoidOps α] [IsCommMagma α] [IsMonoid α] (f: ι -> α) (h: ∀i, f i = 1) : ∏i, f i = 1 :=
  sum_eq_zero (α := AddOfMul α) _ h

def prod_eq_zero [Zero α] [One α] [Mul α] [IsMulZeroClass α] [IsCommMagma α] [IsSemigroup α] (f: ι -> α) (h: ∃i, f i = 0) : ∏i, f i = 0 := by
  apply Multiset.prod_eq_zero
  rw [Multiset.mem_map]
  obtain ⟨i, eq⟩ := h
  exists i
  apply And.intro
  apply Finset.mem_univ
  assumption

def sum_eq_of_equiv [Zero α] [Add α] [IsAddSemigroup α] [IsAddCommMagma α]
  (f: ι₀ -> α) (g: ι₁ -> α) (h: ι₀ ≃ ι₁) (eq: ∀i, f i = g (h i)) : ∑i, f i = ∑i, g i := by
  unfold sum
  conv => { lhs; arg 1; arg 1; intro i; rw [eq] }
  rw [←Function.comp_def, ←Multiset.map_map]
  congr
  show (Fintype.ofEquiv' h).all.val = _
  congr
  apply Subsingleton.allEq

def prod_eq_of_equiv [One α] [Mul α] [IsSemigroup α] [IsCommMagma α]
  (f: ι₀ -> α) (g: ι₁ -> α) (h: ι₀ ≃ ι₁) (eq: ∀i, f i = g (h i)) : ∏i, f i = ∏i, g i :=
  sum_eq_of_equiv (α := AddOfMul α) _ _ h eq

def sum_congr [Zero α] [Add α] [IsAddSemigroup α] [IsAddCommMagma α]
  (f g: ι -> α) (eq: ∀i, f i = g i) : ∑i, f i = ∑i, g i := by
  apply sum_eq_of_equiv _ _ .rfl
  assumption

def prod_congr [One α] [Mul α] [IsSemigroup α] [IsCommMagma α]
  (f g: ι -> α) (eq: ∀i, f i = g i) : ∏i, f i = ∏i, g i := by
  apply prod_eq_of_equiv _ _ .rfl
  assumption

def sum_reindex [Zero α] [Add α] [IsAddSemigroup α] [IsAddCommMagma α]
  (f: ι₁ -> α) (h: ι₀ ≃ ι₁) : ∑i, f i = ∑i, f (h i) := by
  apply sum_eq_of_equiv _  _ h.symm
  intro;
  rw [Equiv.symm_coe]

def prod_reindex [One α] [Mul α] [IsSemigroup α] [IsCommMagma α]
  (f: ι₁ -> α) (h: ι₀ ≃ ι₁) : ∏i, f i = ∏i, f (h i) := by
  apply prod_eq_of_equiv _  _ h.symm
  intro;
  rw [Equiv.symm_coe]

def sum_empty [IsEmpty ι'] [Zero α] [Add α] [IsAddSemigroup α] [IsAddCommMagma α] (f: ι' -> α) : ∑i, f i = 0 := rfl
def sum_option [Zero α] [Add α] [IsAddZeroClass α] [IsAddSemigroup α] [IsAddCommMagma α] (f: Option ι -> α) : ∑i, f i = f .none + ∑i, f (.some i) := by
  rw [sum]
  simp [Finset.univ, Fintype.all, Fintype.instOption, Fintype.ofEquiv, Fintype.ofEquiv',
    Finset.map_emb, Function.comp_def, Finset.union_disjoint]
  rw [←Finset.univ]
  simp [Multiset.map_append, Multiset.sum_append]
  rfl
def sum_succ [Zero α] [Add α] [IsAddZeroClass α] [IsAddSemigroup α] [IsAddCommMagma α] (f: Fin (n + 1) -> α) : ∑i, f i = f (Fin.last _) + ∑i: Fin n, f i.castSucc := by
  rw [sum_reindex (h := (Equiv.fin_equiv_option n).symm), sum_option]
  rfl

def prod_empty [IsEmpty ι'] [One α] [Mul α] [IsSemigroup α] [IsCommMagma α] (f: ι' -> α) : ∏i, f i = 1 := rfl
def prod_option [One α] [Mul α] [IsMulOneClass α] [IsSemigroup α] [IsCommMagma α] (f: Option ι -> α) : ∏i, f i = f .none * ∏i, f (.some i) :=
  sum_option (α := AddOfMul α) f
def prod_succ [One α] [Mul α] [IsMulOneClass α] [IsSemigroup α] [IsCommMagma α] (f: Fin (n + 1) -> α) : ∏i, f i = f (Fin.last _) * ∏i: Fin n, f i.castSucc :=
  sum_succ (α := AddOfMul α) f

def sum_const [AddMonoidOps α] [IsAddMonoid α] [IsAddCommMagma α] (x: α) : ∑_: ι, x = Fintype.card ι • x := by
  unfold sum
  rw [show Multiset.map _ _ = Multiset.replicate (Fintype.card ι) x from ?_,
    Multiset.sum_replicate]
  rw [Multiset.map_const_eq_replicate]
  rfl

def prod_const [MonoidOps α] [IsMonoid α] [IsCommMagma α] (x: α) : ∏_: ι, x = x ^ Fintype.card ι :=
  sum_const (α := AddOfMul α) _

-- def sum_sum [AddMonoidOps α] [IsAddMonoid α] [IsAddCommMagma α] (f: ι₀ -> ι₁ -> α) :
--   ∑i j, f i j = ∑i: ι₀ × ι₁, f i.1 i.2 := by
--   sorry
