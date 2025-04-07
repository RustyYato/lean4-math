import Math.Data.Fintype.Cases
import Math.Data.Multiset.Algebra
import Math.Data.Nat.Factorial
import Init.Notation

variable [Fintype ι] [Fintype ι₀] [Fintype ι₁]

def sum [Zero α] [Add α] [IsAddSemigroup α] [IsAddCommMagma α] (f: ι -> α) : α := ((Finset.univ ι).val.map f).sum
def prod [One α] [Mul α] [IsSemigroup α] [IsCommMagma α] (f: ι -> α) : α := sum (α := AddOfMul α) f

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
def sum_succ' [Zero α] [Add α] [IsAddZeroClass α] [IsAddSemigroup α] [IsAddCommMagma α] (f: Fin (n + 1) -> α) : ∑i, f i = f 0 + ∑i: Fin n, f i.succ := by
  rw [sum_reindex (h := Equiv.fin_rev), sum_succ, sum_reindex (h := Equiv.fin_rev), ]
  congr
  show Fin.rev _ = _
  rw [Fin.rev_last]
  ext i
  congr
  show Fin.rev i.rev.castSucc = _
  rw [Fin.rev_castSucc, Fin.rev_rev]
def sum_sumty [Zero α] [Add α] [IsAddZeroClass α] [IsAddSemigroup α] [IsAddCommMagma α] (f: ι₀ ⊕ ι₁ -> α) : ∑i, f i = (∑i, f (.inl i)) + ∑i, f (.inr i) := by
  rename Fintype ι₀ => ft₀
  induction ft₀ using Fintype.typeInduction with
  | empty => rw [sum_empty, zero_add, sum_reindex (h := Equiv.empty_sum_eqv.symm)]; rfl
  | option ι₀ ft₀ ih =>
    rw [sum_reindex (h := Equiv.option_sum_eqv.symm),
      sum_option, sum_option, ih]; clear ih
    rw [add_assoc]
    rfl
  | eqv α β eqv _ ih =>
    let ft := Fintype.ofEquiv' eqv
    rw [sum_reindex (h := Equiv.congrSum eqv .rfl), ih,
      sum_reindex (h := eqv)]
    rfl
def prod_sumty  [One α] [Mul α] [IsMulOneClass α] [IsSemigroup α] [IsCommMagma α] (f: ι₀ ⊕ ι₁ -> α) : ∏i, f i = (∏i, f (.inl i)) * ∏i, f (.inr i) :=
  sum_sumty (α := AddOfMul α) _

def prod_empty [IsEmpty ι'] [One α] [Mul α] [IsSemigroup α] [IsCommMagma α] (f: ι' -> α) : ∏i, f i = 1 := rfl
def prod_option [One α] [Mul α] [IsMulOneClass α] [IsSemigroup α] [IsCommMagma α] (f: Option ι -> α) : ∏i, f i = f .none * ∏i, f (.some i) :=
  sum_option (α := AddOfMul α) f
def prod_succ [One α] [Mul α] [IsMulOneClass α] [IsSemigroup α] [IsCommMagma α] (f: Fin (n + 1) -> α) : ∏i, f i = f (Fin.last _) * ∏i: Fin n, f i.castSucc :=
  sum_succ (α := AddOfMul α) f
def prod_succ' [One α] [Mul α] [IsMulOneClass α] [IsSemigroup α] [IsCommMagma α] (f: Fin (n + 1) -> α) : ∏i, f i = f 0 * ∏i: Fin n, f i.succ :=
  sum_succ' (α := AddOfMul α) f

def sum_const [AddMonoidOps α] [IsAddMonoid α] [IsAddCommMagma α] (x: α) : ∑_: ι, x = Fintype.card ι • x := by
  unfold sum
  rw [show Multiset.map _ _ = Multiset.replicate (Fintype.card ι) x from ?_,
    Multiset.sum_replicate]
  rw [Multiset.map_const_eq_replicate]
  rfl

def prod_const [MonoidOps α] [IsMonoid α] [IsCommMagma α] (x: α) : ∏_: ι, x = x ^ Fintype.card ι :=
  sum_const (α := AddOfMul α) _

def sum_sum [AddMonoidOps α] [IsAddMonoid α] [IsAddCommMagma α] (f: ι₀ -> ι₁ -> α) :
  ∑i j, f i j = ∑i: ι₀ × ι₁, f i.1 i.2 := by
  rename_i ft₀ ft₁ _ _ _
  induction ft₀ using Fintype.typeInduction with
  | empty => rw [sum_empty, sum_empty]
  | option ι₀ ft₀ ih =>
    rw [sum_option, ih]; clear ih
    rw [sum_reindex (h := Equiv.option_prod_equiv_sum_prod.symm),
      sum_sumty]
    congr
  | eqv α β eqv _ ih =>
    let ft := Fintype.ofEquiv' eqv
    rw [sum_reindex (h := eqv), ih]
    rw [sum_reindex (h := Equiv.congrProd eqv .rfl)]
    rfl

def prod_prod [MonoidOps α] [IsMonoid α] [IsCommMagma α] (f: ι₀ -> ι₁ -> α) :
  ∏i j, f i j = ∏i: ι₀ × ι₁, f i.1 i.2 :=
  sum_sum (α := AddOfMul α) f

def sum_select [AddMonoidOps α] [IsAddMonoid α] [IsAddCommMagma α] [∀i: ι, Decidable (i = i₀)] (f: ι -> α) :
  (∑i, if i = i₀ then f i else 0) = f i₀ := by
  rw [sum_reindex (h := (Equiv.remove i₀).symm), sum_option,
    sum_eq_zero, add_zero]
  rw [if_pos]
  rfl
  rfl
  intro ⟨i, hi⟩
  simp; intro g
  contradiction

def sum_select_unique [AddMonoidOps α] [IsAddMonoid α] [IsAddCommMagma α] (f: ι -> α) (i₀: ι) [∀i: ι, Decidable (i = i₀)] (fi: ι -> Prop) [decfi: DecidablePred fi]
  (fi_spec: ∀i, fi i ↔ i = i₀) :
  (∑i, if fi i then f i else 0) = f i₀ := by
  rw [sum_reindex (h := (Equiv.remove i₀).symm), sum_option,
    sum_eq_zero, add_zero]
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
  (g: F) (f: ι -> α) :
  g (∑i: ι, f i) = ∑i: ι, g (f i)  := by
  rename Fintype ι => ft
  unfold sum
  rw [Multiset.map_sum, Multiset.map_map]
  rfl

def map_prod
  [MonoidOps α] [IsMonoid α] [IsCommMagma α]
  [MonoidOps β] [IsMonoid β] [IsCommMagma β]
  [FunLike F α β] [IsOneHom F α β] [IsMulHom F α β]
  (g: F) (f: ι -> α) :
  g (∏i: ι, f i) = ∏i: ι, g (f i)  :=
  map_sum (α := AddOfMul α) (β := AddOfMul β) g f

def mul_sum  [AddMonoidOps α] [Mul α] [IsAddMonoid α] [IsAddCommMagma α] [IsLeftDistrib α] [IsMulZeroClass α] (x: α) (f: ι -> α) :
  x * ∑i: ι, f i = ∑i: ι, x * f i  := by
  let g : α →+ α := {
    toFun a := x * a
    map_add := mul_add _ _ _
    map_zero := mul_zero _
  }
  show g (∑i: ι, f i) = _
  rw [map_sum]
  rfl

def sum_mul [AddMonoidOps α] [Mul α] [IsAddMonoid α] [IsAddCommMagma α] [IsRightDistrib α] [IsMulZeroClass α] (x: α) (f: ι -> α) :
  (∑i: ι, f i) * x = ∑i: ι, f i * x  := by
  let g : α →+ α := {
    toFun a := a * x
    map_add := add_mul _ _ _
    map_zero := zero_mul _
  }
  show g (∑i: ι, f i) = _
  rw [map_sum]
  rfl

def smul_sum [SMul β α] [AddMonoidOps α] [Mul α] [IsAddMonoid α] [IsAddCommMagma α]
  [MonoidOps β] [IsMonoid β] [IsDistribMulAction β α] (x: β) (f: ι -> α) :
  x • (∑i: ι, f i) = ∑i: ι, x • f i  := by
  let g : α →+ α := {
    toFun a := x • a
    map_add := smul_add _ _ _
    map_zero := smul_zero _
  }
  show g (∑i: ι, f i) = _
  rw [map_sum]
  rfl

def neg_sum [AddGroupOps α] [Mul α] [IsAddGroup α] [IsAddCommMagma α] (f: ι -> α) :
  -∑i, f i = ∑i, -f i := by
  let g : α →+ α := {
    toFun a := -a
    map_add := by
      intro a b
      simp [neg_add_rev, add_comm]
    map_zero := neg_zero
  }
  show g (∑i: ι, f i) = _
  rw [map_sum]
  rfl

def sum_add_sum [AddMonoidOps α] [IsAddMonoid α] [IsAddCommMagma α] (f g: ι -> α) : (∑i, f i) + (∑i, g i) = ∑i, f i + g i := by
  apply Multiset.sum_pairwise

def sum_sub_sum [AddGroupOps α] [Mul α] [IsAddGroup α] [IsAddCommMagma α] (f g: ι -> α) : (∑i, f i) - (∑i, g i) = ∑i, f i - g i := by
  rw [sub_eq_add_neg, neg_sum, sum_add_sum]
  congr; ext i; rw [sub_eq_add_neg]

def fact_eq_prod (n: ℕ) : n ! = ∏i: Fin n, i.val + 1 := by
  induction n with
  | zero => simp [prod_empty]
  | succ n ih => simp [prod_succ, ih]
