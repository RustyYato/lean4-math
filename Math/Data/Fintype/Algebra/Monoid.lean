import Math.Data.Fintype.Defs
import Math.Algebra.Monoid.Hom
import Math.Data.Nat.Factorial
import Init.Notation

def sum [Fintype ι] [Zero α] [Add α] [IsAddSemigroup α] [IsAddCommMagma α] (f: ι -> α) : α :=
  Fintype.fold (fun i a => f i + a) 0 (by intro a b c; dsimp; ac_rfl)
def prod [Fintype ι] [One α] [Mul α] [IsSemigroup α] [IsCommMagma α] (f: ι -> α) : α := sum (α := AddOfMul α) f

section Syntax

open Lean
open TSyntax.Compat

macro "∑ " xs:explicitBinders ", " b:term:60 : term => expandExplicitBinders ``sum xs b
macro "∏ " xs:explicitBinders ", " b:term:60 : term => expandExplicitBinders ``prod xs b

@[app_unexpander sum] def unexpand_sum : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => ∑ $xs:binderIdent*, $b) => `(∑ $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                     => `(∑ $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)              => `(∑ ($x:ident : $t), $b)
  | _                                              => throw ()

@[app_unexpander prod] def unexpand_prod : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => ∏ $xs:binderIdent*, $b) => `(∏ $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                     => `(∏ $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)              => `(∏ ($x:ident : $t), $b)
  | _                                              => throw ()

end Syntax

section

variable [Zero α] [Add α] [IsAddSemigroup α] [IsAddCommMagma α]

@[simp]
def sum_empty [IsEmpty ι] {fι: Fintype ι} (f: ι -> α) : ∑i, f i = 0 := by
  rw [Subsingleton.allEq fι (Fintype.instOfIsEmpty (α := ι))]
  apply Fintype.fold_empty

variable [Fintype ι] [Fintype ι₀] [Fintype ι₁] [IsAddZeroClass α]

@[simp]
def sum_option {fι: Fintype (Option ι)} (f: Option ι -> α) : ∑i, f i = f none + ∑i: ι, f i := by
  rw [Subsingleton.allEq fι (Fintype.instOption (α := ι))]
  apply Fintype.fold_option
def sum_eqv (h: ι₀ ≃ ι₁) (f: ι₁ -> α) : ∑i, f i = ∑i, f (h i) := by
  apply Fintype.fold_eqv

def sum_zero (f: Fin 0 -> α) : ∑i, f i = 0 := rfl
def sum_succ_last (f: Fin (n + 1) -> α) : ∑i, f i = f (.last _) + ∑i: Fin n, f i.castSucc := by
  rw [sum_eqv (Equiv.fin_equiv_option _).symm, sum_option]
  congr
  simp
def sum_succ (f: Fin (n + 1) -> α) : ∑i, f i = f 0 + ∑i: Fin n, f i.succ := by
  rw [sum_eqv Equiv.fin_rev, sum_succ_last, sum_eqv Equiv.fin_rev]
  congr
  simp [Equiv.fin_rev, Equiv.ofInvolut]
  ext i; congr
  simp [Equiv.fin_rev, Equiv.ofInvolut]
  rw [Fin.rev_castSucc, Fin.rev_rev]

def sum_congr (f g: ι -> α) (eq: ∀i, f i = g i) : ∑i, f i = ∑i, g i := by rw [funext eq]
def sum_sumty (f: ι₀ ⊕ ι₁ -> α) : ∑i, f i = (∑i, f (.inl i)) + ∑i, f (.inr i) := by
  rename_i fι _ _
  induction fι with
  | empty =>
    simp
    rw [sum_eqv (Equiv.empty_sum_eqv (α := PEmpty) (β := ι₁)).symm]
    rfl
  | option α ih =>
    rw [sum_eqv Equiv.option_sum_eqv.symm]
    simp [add_assoc, ih]
    rfl
  | eqv α β h ih =>
    rw [sum_eqv h, sum_eqv (Equiv.congrSum h .rfl), ih]
    rfl
def sum_sum (f: ι₀ -> ι₁ -> α) : ∑i j, f i j = ∑i: ι₀ × ι₁, f i.1 i.2 := by
  rename_i fι _ _
  induction fι with
  | empty => simp
  | option α ih =>
    rw [sum_eqv Equiv.option_prod_equiv_sum_prod.symm,
      sum_sumty]
    simp [ih]
    rfl
  | eqv α β h ih =>
    rw [sum_eqv h, ih, sum_eqv (Equiv.congrProd h .rfl)]
    rfl

def sum_eq_of_equiv
  (f: ι₀ -> α) (g: ι₁ -> α) (h: ι₀ ≃ ι₁) (eq: ∀i, f i = g (h i)) : ∑i, f i = ∑i, g i := by
  rw [sum_eqv h, sum_congr]
  assumption

def sum_eq_zero (f: ι -> α) (hf: ∀i, f i = 0) : ∑i, f i = 0 := by
  rename_i fι _ _ _
  induction fι with
  | empty => simp
  | option _ ih =>
    rw [sum_option, ih (fun i => f (some i)), hf, add_zero]
    intro; apply hf
  | eqv α β h ih =>
    rw [sum_eqv h, ih]
    intro; apply hf

end

section

variable [One α] [Mul α] [IsSemigroup α] [IsCommMagma α]

@[simp]
def prod_empty [IsEmpty ι] {fι: Fintype ι} (f: ι -> α) : ∏i, f i = 1 :=
  sum_empty (α := AddOfMul α) _

variable [Fintype ι] [Fintype ι₀] [Fintype ι₁] [IsMulOneClass α]

@[simp]
def prod_option {fι: Fintype (Option ι)} (f: Option ι -> α) : ∏i, f i = f none * ∏i: ι, f i :=
  sum_option (α := AddOfMul α) _
def prod_eqv (h: ι₀ ≃ ι₁) (f: ι₁ -> α) : ∏i, f i = ∏i, f (h i) :=
  sum_eqv (α := AddOfMul α) _ _

def prod_zero (f: Fin 0 -> α) : ∏i, f i = 1 := rfl
def prod_succ_last (f: Fin (n + 1) -> α) : ∏i, f i = f (.last _) * ∏i: Fin n, f i.castSucc :=
  sum_succ_last (α := AddOfMul α) _
def prod_succ (f: Fin (n + 1) -> α) : ∏i, f i = f 0 * ∏i: Fin n, f i.succ :=
  sum_succ (α := AddOfMul α) _

def prod_congr (f g: ι -> α) (eq: ∀i, f i = g i) : ∏i, f i = ∏i, g i := by rw [funext eq]
def prod_sumty (f: ι₀ ⊕ ι₁ -> α) : ∏i, f i = (∏i, f (.inl i)) * ∏i, f (.inr i) :=
   sum_sumty (α := AddOfMul α) _
def prod_prod (f: ι₀ -> ι₁ -> α) : ∏i j, f i j = ∏i: ι₀ × ι₁, f i.1 i.2 :=
  sum_sum (α := AddOfMul α) _

def prod_eq_of_equiv
  (f: ι₀ -> α) (g: ι₁ -> α) (h: ι₀ ≃ ι₁) (eq: ∀i, f i = g (h i)) : ∏i, f i = ∏i, g i := by
  rw [prod_eqv h, prod_congr]
  assumption

def prod_eq_one (f: ι -> α) (hf: ∀i, f i = 1) : ∏i, f i = 1 :=
  sum_eq_zero (α := AddOfMul α) _ hf
def prod_eq_zero [Zero α] [IsMulZeroClass α] (f: ι -> α) (hf: ∃i, f i = 0) : ∏i, f i = 0 := by
  obtain ⟨i, hi⟩ := hf
  classical
  have := Fintype.ofEquiv' (Equiv.erase i)
  rw [prod_eqv (Equiv.erase i).symm, prod_option]
  simp [Equiv.erase]; rw [hi, zero_mul]

end

variable [fι: Fintype ι] [Fintype ι₀] [Fintype ι₁]

@[simp]
def sum_const [AddMonoidOps α] [IsAddMonoid α] [IsAddCommMagma α] (a: α) : ∑_: ι, a = Fintype.card ι • a := by
  induction fι with
  | empty => simp
  | option _ ih => simp [ih, succ_nsmul, add_comm]
  | eqv _ _ h ih => rw [sum_eqv h, ih, Fintype.card_eq_of_equiv h]

@[simp]
def prod_const [MonoidOps α] [IsMonoid α] [IsCommMagma α] (a: α) : ∏_: ι, a = a ^ Fintype.card ι :=
  sum_const (α := AddOfMul α) _

def sum_select [AddMonoidOps α] [IsAddMonoid α] [IsAddCommMagma α] [∀i: ι, Decidable (i = i₀)] (f: ι -> α) :
  (∑i, if i = i₀ then f i else 0) = f i₀ := by
  have := Fintype.ofEquiv' (Equiv.erase i₀)
  rw [sum_eqv (Equiv.erase i₀).symm, sum_option]
  simp [Equiv.erase]; rw [sum_eq_zero, add_zero]
  intro i
  simp [i.property]

def sum_select_unique [AddMonoidOps α] [IsAddMonoid α] [IsAddCommMagma α] (f: ι -> α) (i₀: ι) [∀i: ι, Decidable (i = i₀)] (fi: ι -> Prop) [decfi: DecidablePred fi]
  (fi_spec: ∀i, fi i ↔ i = i₀) :
  (∑i, if fi i then f i else 0) = f i₀ := by
  have := Fintype.ofEquiv' (Equiv.remove i₀)
  rw [sum_eqv (h := (Equiv.remove i₀).symm), sum_option, sum_eq_zero, add_zero]
  rw [if_pos]
  rfl
  show fi i₀
  exact (fi_spec _).mpr rfl
  intro ⟨i, hi⟩
  simp; intro g
  rw [fi_spec] at g
  contradiction

def map_sum
  [AddMonoidOps α] [IsAddMonoid α] [IsAddCommMagma α]
  [AddMonoidOps β] [IsAddMonoid β] [IsAddCommMagma β]
  [FunLike F α β] [IsZeroHom F α β] [IsAddHom F α β]
  (g: F) (f: ι -> α) : g (∑i, f i) = ∑i, g (f i) := by
  induction fι with
  | empty => simp [map_zero]
  | option _ ih => simp [map_add, ih]
  | eqv α β h ih => rw [sum_eqv h, sum_eqv h, ih]

def map_prod
  [MonoidOps α] [IsMonoid α] [IsCommMagma α]
  [MonoidOps β] [IsMonoid β] [IsCommMagma β]
  [FunLike F α β] [IsOneHom F α β] [IsMulHom F α β]
  (g: F) (f: ι -> α) : g (∏i, f i) = ∏i, g (f i) :=
  map_sum (α := AddOfMul α) (β := AddOfMul β) g f

def sum_pairwise [AddMonoidOps α] [IsAddMonoid α] [IsAddCommMagma α] (f g: ι -> α) : (∑i, f i) + (∑i, g i) = ∑i, f i + g i := by
  induction fι with
  | empty => simp
  | option _ ih =>
    simp [← ih]
    ac_nf
  | eqv α β h ih => simp [sum_eqv h, ih]

def prod_pairwise [MonoidOps α] [IsMonoid α] [IsCommMagma α] (f g: ι -> α) : (∏i, f i) * (∏i, g i) = ∏i, f i * g i :=
  sum_pairwise (α := AddOfMul α) _ _

def fact_eq_prod (n: ℕ) : n ! = ∏i: Fin n, i.val + 1 := by
  induction n with
  | zero => simp [prod_empty]
  | succ n ih => simp [prod_succ_last, ih]
