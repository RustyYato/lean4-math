import Math.Algebra.Semiring.Defs
import Math.Algebra.Monoid.Action.Defs
import Math.Algebra.Monoid.SetLike.Defs

namespace List

def prod [Mul α] [One α] : List α -> α := List.sum (α := AddOfMul α)

def sum_extract
  [Add α] [Zero α] [IsAddSemigroup α]
  [IsAddZeroClass α] [IsAddCommMagma α]
  (as bs: List α) (x: α):
  (as ++ x::bs).sum = x + (as ++ bs).sum := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp [List.cons_append, List.sum_cons]
    rw [add_left_comm, ih]

def sum_append
  [Zero α] [Add α] [IsAddSemigroup α] [IsAddZeroClass α]
  (as bs: List α) : (as ++ bs).sum = as.sum + bs.sum := by
  induction as with
  | nil => symm; apply zero_add
  | cons a as ih => simp [List.cons_append, List.sum_cons, ih, add_assoc]

def sum_strip_prefix_zeros
  [Zero α] [Add α] [IsAddZeroClass α] (as bs: List α) : (∀a ∈ as, a = 0) -> (as ++ bs).sum = bs.sum := by
  induction as with
  | nil => intro; rfl
  | cons a as ih =>
    intro h
    rw [List.cons_append, sum_cons, ih, h a, zero_add]
    apply List.Mem.head
    intro a ha
    exact h _ (List.Mem.tail _ ha)

def prod_strip_prefix_zeros
  [One α] [Mul α] [IsMulOneClass α] (as bs: List α) : (∀a ∈ as, a = 1) -> (as ++ bs).prod = bs.prod :=
  sum_strip_prefix_zeros (α := AddOfMul α) as bs

def sum_eq_zero_of_all_zeros
  [Zero α] [Add α] [IsAddZeroClass α] (as: List α) : (∀a ∈ as, a = 0) -> as.sum = 0 := by
  intro h
  rw [←List.append_nil as]
  apply sum_strip_prefix_zeros as []
  assumption

def prod_eq_one_of_all_one
  [One α] [Mul α] [IsMulOneClass α] (as: List α) : (∀a ∈ as, a = 1) -> as.prod = 1 :=
  sum_eq_zero_of_all_zeros (α := AddOfMul α) as

def sum_mul
  [Zero α] [Add α] [Mul α] [IsMulZeroClass α] [IsRightDistrib α]
  (as: List α) (k: α) :
  as.sum * k = sum (as.map (fun x => x * k)) := by
  induction as with
  | nil => apply zero_mul
  | cons a as ih => simp [add_mul, ih]

def mul_sum
  [Zero α] [Add α] [Mul α] [IsMulZeroClass α] [IsLeftDistrib α]
  (as: List α) (k: α) :
  k * as.sum = sum (as.map (fun x => k * x)) := by
  induction as with
  | nil => apply mul_zero
  | cons a as ih => simp [mul_add, ih]

def smul_sum
  [MonoidOps β] [IsMonoid β] [AddMonoidOps α] [IsAddMonoid α] [SMul β α] [IsDistribMulAction β α]
  (as: List α) (k: β) :
  k • as.sum = sum (as.map (fun i => k • i)) := by
  induction as with
  | nil => apply smul_zero
  | cons a as ih =>
    dsimp
    rw [smul_add, ih]

def map_sum_map
  [Add β] [Zero β] [IsAddZeroClass β] [IsAddCommMagma β] [IsAddSemigroup β]
  (as: List α) (f g: α -> β) : (as.map f).sum + (as.map g).sum = (as.map (fun x => f x + g x)).sum := by
  induction as with
  | nil => apply add_zero
  | cons a as ih =>
    simp [←ih]
    ac_rfl

end List

def mem_list_sum [SetLike S α] [Add α] [Zero α ] [IsAddSubmonoid S] (as: List α) (s: S) (h: ∀x ∈ as, x ∈ s) : as.sum ∈ s := by
  induction as with
  | nil => apply mem_zero
  | cons a as ih =>
    apply mem_add
    apply h
    apply List.Mem.head
    apply ih
    intro x hx
    apply h
    apply List.Mem.tail
    assumption
