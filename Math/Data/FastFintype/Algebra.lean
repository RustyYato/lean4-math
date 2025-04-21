import Math.Algebra.Ring.Defs
import Math.Algebra.Module.Defs
import Math.Algebra.Hom.Defs
import Math.Data.FastFintype.Basic

section

variable [Fintype ι] [Fintype ι₀] [Fintype ι₁]

section

variable [Zero α] [Add α] [IsAddSemigroup α] [IsAddCommMagma α]

private def Fin.sum (f: Fin n -> α) : α :=
  Fin.foldr n (fun n a => f n + a) 0

@[simp]
private def Fin.sum_zero (f: Fin 0 -> α) :
  sum f = 0 := rfl
private def Fin.sum_succ (f: Fin (n + 1) -> α) :
  sum f = f 0 + sum (f ∘ succ) := foldr_succ _ _
private def Fin.sum_succ' (f: Fin (n + 1) -> α) :
  sum f = f (Fin.last _) + sum (f ∘ castSucc) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sum_succ, ih, add_left_comm]
    congr 1
    rw [sum_succ]
    rfl

private def Fin.sum_extract (f: Fin (n + 1) -> α) (i: Fin (n + 1)) :
  Fin.sum f = f i + Fin.sum (fun j: Fin n => if j.val < i.val then f j.castSucc else f j.succ) := by
  induction n with
  | zero =>
    simp  [Fin.sum_succ]
    congr; apply Subsingleton.allEq (α := Fin 1)
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      rw [Fin.sum_succ]
      congr
    | succ i =>
      rw [Fin.sum_succ, ih _ i]
      rw [add_left_comm]
      congr
      rw [Fin.sum_succ]
      simp; rfl

private def Fin.sum_extract' (f: Fin (n + 1) -> α) (i: Fin (n + 1)) :
  sum f = sum (f ∘ Equiv.rotateRange 0 i i.val) := by
  rw [sum_extract _ i, sum_succ]
  simp [Equiv.swap_spec]
  congr
  rw [Equiv.rotateRange_of_between]
  ext; simp
  rw [Nat.mod_eq_of_lt]
  omega
  repeat apply Nat.zero_le
  ext j
  split
  rw [Equiv.rotateRange_of_between]
  congr; ext; simp
  rw [Nat.add_assoc, Nat.add_comm 1, Nat.add_mod_right,
    Nat.mod_eq_of_lt]
  omega
  repeat apply Nat.zero_le
  show j.val + 1 ≤ i.val
  omega
  rename_i h
  simp at h
  rw [Equiv.rotateRange_of_gt]
  apply Nat.zero_le
  show i.val < j.val + 1
  omega

private def Fin.sum_rotate_last (f: Fin n -> α) :
  sum f = sum (f ∘ Equiv.rotate _ 1) := by
  cases n
  rfl
  rw [Fin.sum_succ, Fin.sum_succ']
  congr
  simp
  simp
  ext i; congr; ext; simp
  rw [Nat.mod_eq_of_lt]
  omega

private def Fin.sum_perm (f: Fin n -> α) (perm: Fin n ≃ Fin n) :
  Fin.sum f = Fin.sum (f ∘ perm) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [
      Fin.sum_succ',
      Fin.sum_extract' (f ∘ perm) (perm.symm (Fin.last n)),
      Fin.sum_rotate_last (n := n + 1),
      Fin.sum_succ']
    congr 1
    simp; congr 1
    rw [Equiv.rotateRange_of_between]
    simp
    conv => {
      rhs; arg 2; arg 1; rw [Nat.mod_eq_of_lt (by omega)]
    }
    simp
    repeat apply Nat.zero_le
    let eqv := perm.comp
      (Equiv.rotateRange 0 (perm.symm (last n)) ↑(perm.symm (last n)))
      |>.comp (Equiv.rotate (n + 1) 1)
    show _ = Fin.sum (f ∘ eqv ∘ castSucc)
    apply ih _ {
      toFun x := ⟨eqv x.castSucc, by
        apply Nat.lt_of_le_of_ne
        omega
        intro h
        replace h: eqv x.castSucc = (Fin.last n).val := h
        rw [Fin.val_inj] at h
        have := Equiv.eq_symm_of_coe_eq eqv h
        unfold eqv at this
        simp at this
        rw [Equiv.symm_rotateRange_of_between] at this
        simp at this
        conv at this => {
          rhs; rhs; arg 1
          conv => {
            arg 1; rw[Nat.mod_eq_of_lt (by omega)]
          }
          rw [Nat.add_sub_cancel_left, Nat.mod_self]
        }
        rw [Equiv.symm_apply_rotate, ←Fin.val_inj] at this
        dsimp at this
        rw [Nat.mod_eq_of_lt (a := 1), Nat.zero_add,
          Nat.add_sub_cancel, Nat.mod_eq_of_lt] at this
        any_goals omega
        any_goals apply Nat.zero_le⟩
      invFun x := ⟨eqv.symm x.castSucc, by
        apply Nat.lt_of_le_of_ne
        omega
        intro h
        replace h: eqv.symm x.castSucc = (Fin.last n).val := h
        rw [Fin.val_inj] at h
        replace h := Equiv.eq_coe_of_symm_eq _ h
        simp [eqv] at h
        rw [Equiv.rotateRange_of_between] at h
        simp at h
        conv at h => {
          rhs; arg 2; arg 1;
          rw [Nat.mod_eq_of_lt (by omega)]
        }
        simp at h
        rw [←Fin.val_inj] at h
        simp at h
        any_goals omega
        any_goals apply Nat.zero_le⟩
      leftInv _ := by simp
      rightInv _ := by simp
    }

end

def sum [Zero α] [Add α] [IsAddSemigroup α] [IsAddCommMagma α] (f: ι -> α) : α :=
  Fintype.hrec (α := ι) (motive := fun _ => α) (fun enc => Fin.sum fun x => f (enc.all x)) <| by
    classical
    intro a b
    simp
    have ⟨eqv, eq⟩ := Fintype.Encoding.equiv a b
    simp [eq]; clear eq
    obtain ⟨acard, h₀, h₁, h₂, h₃⟩ := a
    dsimp; dsimp at eqv
    cases Fin.eq_of_equiv eqv
    clear h₀ h₁ h₂ h₃
    symm; apply Fin.sum_perm
def prod [One α] [Mul α] [IsSemigroup α] [IsCommMagma α] (f: ι -> α) : α := sum (α := AddOfMul α) f

end

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

@[simp] def sum_empty [IsEmpty ι] {fι: Fintype ι} [Zero α] [Add α] [IsAddSemigroup α] [IsAddCommMagma α] (f: ι -> α) : ∑i, f i = 0 := by
  rw [Subsingleton.allEq fι Fintype.instIsEmpty]
  rfl
@[simp] def sum_option {fopt: Fintype (Option ι)} [fι: Fintype ι] [Zero α] [Add α] [IsAddSemigroup α] [IsAddCommMagma α]
  (f: Option ι -> α) : ∑i, f i = f .none + ∑i, f (.some i) := by
  rw [Subsingleton.allEq fopt (Fintype.instOption (α := ι))]
  induction fι
  apply Fin.sum_succ
@[simp] def prod_empty [IsEmpty ι] {fι: Fintype ι} [One α] [Mul α] [IsSemigroup α] [IsCommMagma α] (f: ι -> α) : ∏i, f i = 1 :=
  sum_empty (α := AddOfMul α) _
@[simp] def prod_option {fopt: Fintype (Option ι)} [fι: Fintype ι] [One α] [Mul α] [IsSemigroup α] [IsCommMagma α] (f: Option ι -> α) : ∏i, f i = f .none * ∏i, f (.some i) :=
  sum_option (α := AddOfMul α) _

def sum_reindex {fι: Fintype ι} [Zero α] [Add α] [IsAddSemigroup α] [IsAddCommMagma α] (f: ι -> α) (eqv: ι₀ ≃ ι) :
  have := Fintype.ofEquiv eqv
  ∑i, f i = ∑i, f (eqv i) := by
  unfold sum
  induction fι with | _ fι =>
  show Fin.sum _ = Fin.sum (fun _ => f (eqv (eqv.symm (fι.all _))))
  simp
  rfl

def prod_reindex {fι: Fintype ι} [One α] [Mul α] [IsSemigroup α] [IsCommMagma α] (f: ι -> α) (eqv: ι₀ ≃ ι) :
  have := Fintype.ofEquiv eqv
  ∏i, f i = ∏i, f (eqv i) :=
  sum_reindex (α := AddOfMul α) _ _

def sum_reindex' {fι₀: Fintype ι₀} {fι₁: Fintype ι₁} [Zero α] [Add α] [IsAddSemigroup α] [IsAddCommMagma α] (f: ι₀ -> α) (eqv: ι₁ ≃ ι₀) : ∑i, f i = ∑i, f (eqv i) := by
  rw [Subsingleton.allEq fι₁]
  apply sum_reindex

def prod_reindex' {fι₀: Fintype ι₀} {fι₁: Fintype ι₁} [One α] [Mul α] [IsSemigroup α] [IsCommMagma α] (f: ι₀ -> α) (eqv: ι₁ ≃ ι₀) : ∏i, f i = ∏i, f (eqv i) :=
  sum_reindex' (α := AddOfMul α) _ _

def sum_eq_of_equiv
  {fι₀: Fintype ι₀} {fι₁: Fintype ι₁}
  [Zero α] [Add α] [IsAddSemigroup α] [IsAddCommMagma α]
  (f: ι₀ -> α) (g: ι₁ -> α) (h: ι₀ ≃ ι₁) (eq: ∀i, f i = g (h i)) : ∑i, f i = ∑i, g i := by
  rw [sum_reindex _ h]
  induction fι₀ using Fintype.typeInduction generalizing ι₁ with
  | empty =>
    have := empty_preimage h.symm
    simp
  | option ι₀ fι₀ ih =>
    induction fι₁ using Fintype.typeInduction with
    | empty =>
      have := empty_preimage h
      simp
    | option ι₁ fι₁ ih =>
      clear ih
      simp
      congr
      apply eq
      ext i
      apply eq
    | resp =>
      congr;
      apply Subsingleton.allEq
      ext i; apply eq
  | resp =>
    congr;
    apply Subsingleton.allEq
    ext i; apply eq

def prod_eq_of_equiv
  {fι₀: Fintype ι₀} {fι₁: Fintype ι₁}
  [One α] [Mul α] [IsSemigroup α] [IsCommMagma α]
  (f: ι₀ -> α) (g: ι₁ -> α) (h: ι₀ ≃ ι₁) (eq: ∀i, f i = g (h i)) : ∏i, f i = ∏i, g i :=
  sum_eq_of_equiv (α := AddOfMul α) _ _ h eq

def sum_congr {f: Fintype ι} [Zero α] [Add α] [IsAddSemigroup α] [IsAddCommMagma α]
  (f g: ι -> α) (eq: ∀i, f i = g i) : ∑i, f i = ∑i, g i := by
  apply sum_eq_of_equiv _ _ .rfl
  assumption

def prod_congr {f: Fintype ι} [One α] [Mul α] [IsSemigroup α] [IsCommMagma α]
  (f g: ι -> α) (eq: ∀i, f i = g i) : ∏i, f i = ∏i, g i := by
  apply prod_eq_of_equiv _ _ .rfl
  assumption

attribute [irreducible] sum

def sum_sumty {fsum: Fintype (ι₀ ⊕ ι₁)} {fι₀: Fintype ι₀} {fι₁: Fintype ι₁} [Zero α] [Add α] [IsAddZeroClass α] [IsAddSemigroup α] [IsAddCommMagma α] (f: ι₀ ⊕ ι₁ -> α) : ∑i, f i = (∑i, f (.inl i)) + ∑i, f (.inr i) := by
  induction fι₀ using Fintype.typeInduction with
  | empty =>
    simp
    rw [sum_reindex _ Equiv.empty_sum_eqv.symm]
    apply sum_eq_of_equiv _ _ .rfl
    intro i; rfl
  | option _ _ ih =>
    rw [sum_reindex _ Equiv.option_sum_eqv.symm]
    simp
    rw [add_assoc]
    congr; apply ih
  | resp ι₀ ι₀' fι₀ fι₀' eqv ih =>
    rw [sum_reindex (eqv := Equiv.congrSum eqv .rfl)]
    rw [Subsingleton.allEq (Fintype.ofEquiv _)]
    show ∑i, (f ∘ eqv.congrSum .rfl) i = _
    rw [ih]
    congr 1
    show ∑i, (f (.inl (eqv i))) = _
    symm; apply sum_reindex' _ eqv

def prod_sumty {fsum: Fintype (ι₀ ⊕ ι₁)} {fι₀: Fintype ι₀} {fι₁: Fintype ι₁} [One α] [Mul α] [IsMulOneClass α] [IsSemigroup α] [IsCommMagma α] (f: ι₀ ⊕ ι₁ -> α) : ∏i, f i = (∏i, f (.inl i)) * ∏i, f (.inr i) :=
  sum_sumty (α := AddOfMul α) f

def sum_const {fι: Fintype ι} [AddMonoidOps α] [IsAddMonoid α] [IsAddCommMagma α] (x: α) : ∑_: ι, x = Fintype.card ι • x := by
  induction fι using Fintype.typeInduction with
  | empty => simp
  | option _ _ ih =>
    simp; rw [succ_nsmul', ih]
  | resp ι₀ ι₁ _ _ h ih =>
    rw [Fintype.card_eq_of_equiv h.symm, ←ih]
    apply sum_eq_of_equiv _ _ h.symm
    intro; rfl

def prod_const {fι: Fintype ι} [MonoidOps α] [IsMonoid α] [IsCommMagma α] (x: α) : ∏_: ι, x = x ^ Fintype.card ι :=
  sum_const (α := AddOfMul α) _

def sum_sum {fprod: Fintype (ι₀ × ι₁)} [fι₀: Fintype ι₀] [Fintype ι₁] [AddMonoidOps α] [IsAddMonoid α] [IsAddCommMagma α] (f: ι₀ -> ι₁ -> α) :
  ∑i j, f i j = ∑i: ι₀ × ι₁, f i.1 i.2 := by
  rw [Subsingleton.allEq fprod Fintype.instProd]
  clear fprod
  induction fι₀ using Fintype.typeInduction with
  | empty => simp
  | option ι₀ fι₀ ih =>
    simp
    rw [ih, sum_reindex _ Equiv.option_prod_equiv_sum_prod.symm,
      sum_sumty]
    rfl
  | resp ι₀ ι₀' fι₀ _ eqv ih =>
    rw [sum_reindex _ eqv]
    rw [Subsingleton.allEq (Fintype.ofEquiv _) fι₀]
    rw [ih]
    apply sum_eq_of_equiv _ _ (Equiv.congrProd eqv.symm .rfl).symm
    intro i
    rfl

def prod_prod {fprod: Fintype (ι₀ × ι₁)} [fι₀: Fintype ι₀] [Fintype ι₁] [MonoidOps α] [IsMonoid α] [IsCommMagma α] (f: ι₀ -> ι₁ -> α) :
  ∏i j, f i j = ∏i: ι₀ × ι₁, f i.1 i.2 :=
  sum_sum (α := AddOfMul α) _

def map_sum
  {fι: Fintype ι}
  [AddMonoidOps α] [IsAddMonoid α] [IsAddCommMagma α]
  [AddMonoidOps β] [IsAddMonoid β] [IsAddCommMagma β]
  [FunLike F α β] [IsZeroHom F α β] [IsAddHom F α β]
  (g: F) (f: ι -> α) :
  g (∑i: ι, f i) = ∑i: ι, g (f i) := by
  induction fι using Fintype.typeInduction with
  | empty => simp; rw [map_zero]
  | option _ _ ih => simp; rw[map_add, ih]
  | resp ι₀ ι₁ _ _ eqv ih =>
    rw [sum_reindex' _ eqv, ih,
      sum_reindex' _ eqv.symm]
    simp
    assumption

def map_prod
  {fι: Fintype ι}
  [MonoidOps α] [IsMonoid α] [IsCommMagma α]
  [MonoidOps β] [IsMonoid β] [IsCommMagma β]
  [FunLike F α β] [IsOneHom F α β] [IsMulHom F α β]
  (g: F) (f: ι -> α) :
  g (∏i: ι, f i) = ∏i: ι, g (f i) :=
  map_sum (α := AddOfMul α) (β := AddOfMul β) _ _

def mul_sum {fι: Fintype ι} [AddMonoidOps α] [Mul α] [IsAddMonoid α] [IsAddCommMagma α] [IsLeftDistrib α] [IsMulZeroClass α] (x: α) (f: ι -> α) :
  x * ∑i: ι, f i = ∑i: ι, x * f i  := by
  let g : α →+ α := {
    toFun a := x * a
    map_add := mul_add _ _ _
    map_zero := mul_zero _
  }
  show g (∑i: ι, f i) = _
  rw [map_sum]
  rfl

def sum_mul {fι: Fintype ι} [AddMonoidOps α] [Mul α] [IsAddMonoid α] [IsAddCommMagma α] [IsRightDistrib α] [IsMulZeroClass α] (x: α) (f: ι -> α) :
  (∑i: ι, f i) * x = ∑i: ι, f i * x  := by
  let g : α →+ α := {
    toFun a := a * x
    map_add := add_mul _ _ _
    map_zero := zero_mul _
  }
  show g (∑i: ι, f i) = _
  rw [map_sum]
  rfl

def smul_sum {fι: Fintype ι} [SMul β α] [AddMonoidOps α] [Mul α] [IsAddMonoid α] [IsAddCommMagma α]
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

def neg_sum {fι: Fintype ι} [AddGroupOps α] [Mul α] [IsAddGroup α] [IsAddCommMagma α] (f: ι -> α) :
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
