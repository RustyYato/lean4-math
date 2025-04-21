import Math.Algebra.Monoid.Defs
import Math.Data.FastFintype.Induction

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
