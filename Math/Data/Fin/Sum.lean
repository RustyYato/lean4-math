import Math.Function.Basic
import Math.Type.Basic
import Math.Algebra.Ring.Basic
import Math.Algebra.Impls.Pi
import Math.Algebra.Hom.Defs

namespace Fin

def sum_from [Add α] (start: α) : ∀{n}, (Fin n -> α) -> α
| 0, _ => start
| _ + 1, f => f 0 + sum_from start (f ∘ Fin.succ)

def sum [Zero α] [Add α] : ∀{n}, (Fin n -> α) -> α := sum_from 0

def prod_from [Mul α] (start: α) : ∀{n}, (Fin n -> α) -> α := sum_from (α := AddOfMul α) start

def prod [One α] [Mul α] : ∀{n}, (Fin n -> α) -> α := sum (α := AddOfMul α)

def sum_from_zero [Add α] (start: α) (f: Fin 0 -> α) : sum_from start f = start := rfl

def prod_from_zero [Mul α] (start: α) (f: Fin 0 -> α) : prod_from start f = start := rfl

def sum_from_succ [Add α] (start: α) (f: Fin (n + 1) -> α) : sum_from start f = f 0 + sum_from start (f ∘ Fin.succ)  := rfl

def prod_from_succ [Mul α] (start: α) (f: Fin (n + 1) -> α) : prod_from start f = f 0 * prod_from start (f ∘ Fin.succ)  := rfl

def sum_zero [Zero α] [Add α] (f: Fin 0 -> α) : sum f = 0 := rfl

def prod_zero [One α] [Mul α] (f: Fin 0 -> α) : prod f = 1 := rfl

def sum_succ [Zero α] [Add α] (f: Fin (n + 1) -> α) : sum f = f 0 + sum (f ∘ Fin.succ) := rfl

def prod_succ [One α] [Mul α] (f: Fin (n + 1) -> α) : prod f = f 0 * prod (f ∘ Fin.succ) := rfl

def sum_from_eq_sum [Zero α] [Add α] [IsAddSemigroup α] [IsAddZeroClass α] (start: α) (f: Fin n -> α) :
  sum_from start f = sum f + start := by
  induction n with
  | zero => symm; apply zero_add
  | succ n ih => rw [sum_from_succ, sum_succ, ih, add_assoc]

def prod_from_eq_prod [One α] [Mul α] [IsSemigroup α] [IsMulOneClass α] (start: α) (f: Fin n -> α) :
  prod_from start f = prod f * start :=
  sum_from_eq_sum (α := AddOfMul α) _ _

def sum_from_succ' [Add α] [IsAddSemigroup α] (start: α) (f: Fin (n + 1) -> α) :
  sum_from start f = sum_from (f (last _)) (fun x => f x.castSucc) + start := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sum_from_succ, ih, ←add_assoc]
    rfl

def sum_succ' [Zero α] [Add α] [IsAddSemigroup α] [IsAddZeroClass α] (f: Fin (n + 1) -> α) :
  sum f = sum (fun x => f x.castSucc) + f (last _) := by
  unfold sum
  rw [sum_from_succ', add_zero, sum_from_eq_sum]
  rfl

def prod_succ' [One α] [Mul α] [IsSemigroup α] [IsMulOneClass α] (f: Fin (n + 1) -> α) :
  prod f = prod (fun x => f x.castSucc) * f (last _) :=
  sum_succ' (α := AddOfMul α) f

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

def sum_from_add_sum_from [Add α] [IsAddSemigroup α] [IsAddCommMagma α] (fs gs: α) (f g: Fin n -> α) : Fin.sum_from fs f + Fin.sum_from gs g = Fin.sum_from (fs + gs) (f + g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sum_from_succ]
    rw [add_assoc, add_left_comm _ (g _), ←add_assoc, ih]
    rfl

def sum_add_sum [Zero α] [Add α] [IsAddZeroClass α] [IsAddSemigroup α] [IsAddCommMagma α] (f g: Fin n -> α) : Fin.sum f + Fin.sum g = Fin.sum (f + g) := by
  rw [sum, sum_from_add_sum_from, add_zero]

def prod_from_mul_prod_from [Mul α] [IsSemigroup α] [IsCommMagma α] (fs gs: α) (f g: Fin n -> α) : Fin.prod_from fs f * Fin.prod_from gs g = Fin.prod_from (fs * gs) (f * g) :=
  sum_from_add_sum_from (α := AddOfMul α) _ _ _ _

def prod_mul_prod [One α] [Mul α] [IsMulOneClass α] [IsSemigroup α] [IsCommMagma α] (f g: Fin n -> α) : Fin.prod f * Fin.prod g = Fin.prod (f * g) :=
  sum_add_sum (α := AddOfMul α) _ _

end Fin
