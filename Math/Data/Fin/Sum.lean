import Math.Function.Basic
import Math.Type.Basic
import Math.Algebra.Ring.Basic
import Math.Algebra.Impls.Pi
import Math.Algebra.Hom.Defs

namespace Fin

def sum_from [Add α] (start: α) : ∀{n}, (Fin n -> α) -> α
| 0, _ => start
| _ + 1, f => sum_from start (f ∘ Fin.castSucc) + f (last _)

def sum [Zero α] [Add α] : ∀{n}, (Fin n -> α) -> α := sum_from 0

def prod_from [Mul α] (start: α) : ∀{n}, (Fin n -> α) -> α := sum_from (α := AddOfMul α) start

def prod [One α] [Mul α] : ∀{n}, (Fin n -> α) -> α := sum (α := AddOfMul α)

def sum_from_zero [Add α] (start: α) (f: Fin 0 -> α) : sum_from start f = start := rfl

def prod_from_zero [Mul α] (start: α) (f: Fin 0 -> α) : prod_from start f = start := rfl

def sum_from_succ [Add α] (start: α) (f: Fin (n + 1) -> α) : sum_from start f = sum_from start (f ∘ Fin.castSucc) + f (last _)  := rfl

def prod_from_succ [Mul α] (start: α) (f: Fin (n + 1) -> α) : prod_from start f = prod_from start (f ∘ Fin.castSucc) * f (last _) := rfl

def sum_zero [Zero α] [Add α] (f: Fin 0 -> α) : sum f = 0 := rfl

def prod_zero [One α] [Mul α] (f: Fin 0 -> α) : prod f = 1 := rfl

def sum_succ [Zero α] [Add α] (f: Fin (n + 1) -> α) : sum f = sum (f ∘ Fin.castSucc) + f (last _) := rfl

def prod_succ [One α] [Mul α] (f: Fin (n + 1) -> α) : prod f = prod (f ∘ Fin.castSucc) * f (last _) := rfl

def sum_from_eq_sum [Zero α] [Add α] [IsAddSemigroup α] [IsAddZeroClass α] (start: α) (f: Fin n -> α) :
  sum_from start f = start + sum f := by
  induction n with
  | zero => symm; apply add_zero
  | succ n ih => rw [sum_from_succ, sum_succ, ih, add_assoc]

def prod_from_eq_prod [One α] [Mul α] [IsSemigroup α] [IsMulOneClass α] (start: α) (f: Fin n -> α) :
  prod_from start f = start * prod f :=
  sum_from_eq_sum (α := AddOfMul α) _ _

def sum_from_succ' [Add α] [IsAddSemigroup α] (start: α) (f: Fin (n + 1) -> α) :
  sum_from start f = start + sum_from (f 0) (f ∘ Fin.succ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sum_from_succ, ih, sum_from_succ, ←add_assoc]
    rfl

def sum_succ' [Zero α] [Add α] [IsAddSemigroup α] [IsAddZeroClass α] (f: Fin (n + 1) -> α) :
  sum f = f 0 + sum (f ∘ Fin.succ) := by
  unfold sum
  rw [sum_from_succ', sum_from_eq_sum, zero_add]
  rfl

def prod_from_succ' [Mul α] [IsSemigroup α] (start: α) (f: Fin (n + 1) -> α) :
  prod_from start f = start * prod_from (f 0) (f ∘ Fin.succ) :=
  sum_from_succ' (α := AddOfMul α) _ _

def prod_succ' [One α] [Mul α] [IsSemigroup α] [IsMulOneClass α] (f: Fin (n + 1) -> α) :
  prod f = f 0 * prod (f ∘ Fin.succ) :=
  sum_succ' (α := AddOfMul α) _

end Fin

section Hom

open Fin

def resp_sum_from [FunLike F α β] [Add α] [Add β] [IsAddHom F α β] (start: α) (f: Fin n -> α) (h: F) : h (Fin.sum_from start f) = Fin.sum_from (h start) (h ∘ f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sum_from_succ, resp_add, ih]
    rfl

def resp_prod_from [FunLike F α β] [Mul α] [Mul β] [IsMulHom F α β] (start: α) (f: Fin n -> α) (h: F) : h (Fin.prod_from start f) = Fin.prod_from (h start) (h ∘ f) :=
  resp_sum_from (α := AddOfMul α) (β := AddOfMul β) start f h

def resp_sum [FunLike F α β] [Zero α] [Zero β] [Add α] [Add β] [IsZeroHom F α β] [IsAddHom F α β] (f: Fin n -> α) (h: F) : h (Fin.sum f) = Fin.sum (h ∘ f) := by
  rw [sum, sum, resp_sum_from, resp_zero]

def resp_prod [FunLike F α β] [One α] [One β] [Mul α] [Mul β] [IsOneHom F α β] [IsMulHom F α β] (f: Fin n -> α) (h: F) : h (Fin.prod f) = Fin.prod (h ∘ f) :=
  resp_sum (α := AddOfMul α) (β := AddOfMul β) f h

end Hom

namespace Fin

def sum_from_ext [Add α] (fs gs: α) (f g: Fin n -> α) :
  fs = gs ->
  (∀x, f x = g x) ->
  Fin.sum_from fs f = Fin.sum_from gs g := by
  rintro rfl h
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sum_from_succ, sum_from_succ, h, ih]
    intro x
    apply h

def sum_ext [Zero α] [Add α] (f g: Fin n -> α) :
  (∀x, f x = g x) ->
  Fin.sum f = Fin.sum g := by
  apply sum_from_ext
  rfl

def sum_from_add_sum_from_pairwise [Add α] [IsAddSemigroup α] [IsAddCommMagma α] (fs gs: α) (f g: Fin n -> α) : Fin.sum_from fs f + Fin.sum_from gs g = Fin.sum_from (fs + gs) (f + g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sum_from_succ]
    rw [add_assoc, add_left_comm _ _ (g _), ←add_assoc, ih]
    rfl

def sum_add_sum_pairwise [Zero α] [Add α] [IsAddZeroClass α] [IsAddSemigroup α] [IsAddCommMagma α] (f g: Fin n -> α) : Fin.sum f + Fin.sum g = Fin.sum (f + g) := by
  rw [sum, sum_from_add_sum_from_pairwise, add_zero]

def prod_from_mul_prod_from_pairwise [Mul α] [IsSemigroup α] [IsCommMagma α] (fs gs: α) (f g: Fin n -> α) : Fin.prod_from fs f * Fin.prod_from gs g = Fin.prod_from (fs * gs) (f * g) :=
  sum_from_add_sum_from_pairwise (α := AddOfMul α) _ _ _ _

def prod_mul_prod_pairwise [One α] [Mul α] [IsMulOneClass α] [IsSemigroup α] [IsCommMagma α] (f g: Fin n -> α) : Fin.prod f * Fin.prod g = Fin.prod (f * g) :=
  sum_add_sum_pairwise (α := AddOfMul α) _ _

def func_append (f: Fin n -> α) (g: Fin m -> α) : Fin (n + m) -> α :=
  fun x =>
    if h:x < n then f ⟨x, h⟩  else g ⟨x.val - n, by
      refine Nat.sub_lt_left_of_lt_add ?_ ?_
      exact Nat.le_of_not_lt h
      exact x.isLt⟩

def sum_from_add_sum [Zero α] [Add α] [IsAddSemigroup α] [IsAddZeroClass α] (fs: α) (f: Fin n -> α) (g: Fin m -> α) : Fin.sum_from fs f + Fin.sum g = Fin.sum_from fs (func_append f g) := by
  induction m with
  | zero =>
    rw [sum_zero, add_zero]
    apply sum_from_ext
    rfl
    intro x
    rw [func_append]
    rw [dif_pos x.isLt]
  | succ m ih =>
    rw [sum_from_succ, sum_succ, ←add_assoc, ih]
    congr
    rw [func_append]
    rw [dif_neg]; unfold last
    congr; dsimp
    rw [Nat.add_sub_cancel_left]
    refine Nat.not_lt.mpr ?_
    apply Nat.le_add_right

def prod_from_mul_prod [One α] [Mul α] [IsSemigroup α] [IsMulOneClass α] (fs: α) (f: Fin n -> α) (g: Fin m -> α) : Fin.prod_from fs f * Fin.prod g = Fin.prod_from fs (func_append f g) :=
  sum_from_add_sum (α := AddOfMul α) _ _ _

def sum_add_sum [Zero α] [Add α] [IsAddSemigroup α] [IsAddZeroClass α] (f: Fin n -> α) (g: Fin m -> α) : Fin.sum f + Fin.sum g = Fin.sum (func_append f g) := by
  apply sum_from_add_sum

def prod_mul_prod [One α] [Mul α] [IsSemigroup α] [IsMulOneClass α] (f: Fin n -> α) (g: Fin m -> α) : Fin.prod f * Fin.prod g = Fin.prod (func_append f g) :=
  sum_add_sum (α := AddOfMul α) _ _

end Fin
