import Math.Data.«Fintype-old».Defs
import Math.Order.Linear

open List

variable (α: Type*) [f: Fintype α] [LT α] [LE α] [IsLinearOrder α] [DecidableLE α]

def sorted_eq_of_perm (as bs: List α) : as ~ bs -> as.Pairwise (· ≤ ·) -> bs.Pairwise (· ≤ ·) -> as = bs := by
  intro perm as_sorted bs_sorted
  induction as_sorted generalizing bs with
  | nil =>
    cases nil_perm.mp perm
    rfl
  | cons =>
    rename_i a as a_le as_sorted ih
    cases bs_sorted with
    | nil => nomatch nil_perm.mp perm.symm
    | cons =>
    rename_i b bs b_le bs_sorted
    suffices a = b by
      subst this
      rw [ih _ perm.cons_inv bs_sorted]
    cases perm.mem_iff.mp (List.Mem.head _)
    rfl
    cases perm.mem_iff.mpr (List.Mem.head _)
    rfl
    apply le_antisymm
    apply a_le
    assumption
    apply b_le
    assumption

def Fintype.sort : List α :=
  f.all.val.lift List.mergeSort <| by
    intro a b h
    apply sorted_eq_of_perm
    apply (mergeSort_perm _ _).trans
    apply Perm.trans _ (mergeSort_perm _ _).symm
    assumption
    simp
    have := sorted_mergeSort (le := (· ≤ ·)) ?_ ?_ a
    conv at this => { left; intro a b ; rw [decide_eq_true_iff] }
    assumption
    intro a b c
    simp
    apply le_trans
    simp
    apply le_total
    have := sorted_mergeSort (le := (· ≤ ·)) ?_ ?_ b
    conv at this => { left; intro a b ; rw [decide_eq_true_iff] }
    assumption
    intro a b c
    simp
    apply le_trans
    simp
    apply le_total

def Fintype.mem_sort : ∀x, x ∈ Fintype.sort α := by
  induction f with
  | mk all nodup complete =>
  intro x
  apply (mergeSort_perm all (· ≤ ·)).mem_iff.mpr
  apply complete

def Fintype.nodup_sort : (Fintype.sort α).Nodup := by
  induction f with
  | mk all nodup complete =>
  apply (mergeSort_perm all (· ≤ ·)).nodup_iff.mpr
  assumption

def Fintype.sorted_sort : (Fintype.sort α).Pairwise (· ≤ ·) := by
  induction f with
  | mk all nodup complete =>
  have := (sorted_mergeSort ?_ ?_ all (le := (· ≤ ·)))
  simp at this
  assumption
  simp; intro _ _ _; apply le_trans
  simp; apply le_total
