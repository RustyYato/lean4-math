import Math.Algebra.Ring.Defs
import Math.Algebra.Module.Defs
import Math.Algebra.Hom.Defs
import Math.Data.Multiset.Basic

namespace Multiset

section

variable [Zero α] [Add α] [IsAddCommMagma α] [IsAddSemigroup α]
variable [One α] [Mul α] [IsCommMagma α] [IsSemigroup α]

def sum (s: Multiset α) : α := by
  refine s.lift ?_ ?_
  apply List.sum
  intro a b eq
  induction eq with
  | nil => rfl
  | trans _ _ ih₀ ih₁ => rw [ih₀, ih₁]
  | cons _ _ ih => rw [List.sum_cons, List.sum_cons, ih]
  | swap a b =>
    rw [List.sum_cons, List.sum_cons, List.sum_cons, List.sum_cons,
      ←add_assoc, add_comm b a, add_assoc]

def prod (s: Multiset α): α :=
  sum (α := AddOfMul α) s

@[simp] def sum_nil : sum ∅ = (0: α) := rfl
@[simp] def sum_cons (a: α) (as: Multiset α) : sum (a::ₘas) = a + sum as := by
  cases as; rfl

@[simp] def prod_nil : prod ∅ = (1: α) := rfl
@[simp] def prod_cons (a: α) (as: Multiset α) : prod (a::ₘas) = a * prod as :=
  sum_cons (α := AddOfMul α) _ _

def sum_append [IsAddZeroClass α] (as bs: Multiset α) : sum (as ++ bs) = sum as + sum bs := by
  induction as with
  | nil => simp
  | cons a as ih => simp [ih, add_assoc]

def prod_append [IsMulOneClass α] (as bs: Multiset α) : prod (as ++ bs) = prod as * prod bs :=
  sum_append (α := AddOfMul α) _ _

end

def sum_eq_zero [AddMonoidOps α] [IsAddCommMagma α] [IsAddMonoid α] (as: Multiset α) : (∀x ∈ as, x = 0) -> as.sum = 0 := by
  intro h
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp [h a (by simp)]; rw [ih ?_]
    intro x hx
    apply h; simp [hx]

def prod_eq_one [MonoidOps α] [IsCommMagma α] [IsMonoid α] (as: Multiset α) : (∀x ∈ as, x = 1) -> as.prod = 1 :=
  sum_eq_zero (α := AddOfMul α) _

def prod_eq_zero [Zero α] [One α] [Mul α] [IsCommMagma α] [IsSemigroup α] [IsMulZeroClass α] (as: Multiset α) : 0 ∈ as -> as.prod = 0 := by
  intro h
  induction as with
  | nil => contradiction
  | cons a as ih =>
    simp
    cases h using Multiset.cases_mem_cons
    simp
    rw [ih]; simp
    assumption

def neg_sum [AddGroupOps α] [IsAddCommMagma α] [IsAddGroup α] (s: Multiset α) : -s.sum = (s.map (-·)).sum := by
  induction s with
  | nil => simp
  | cons a as ih => simp [neg_add_rev, add_comm, ih]

def inv_prod [GroupOps α] [IsCommMagma α] [IsGroup α] (s: Multiset α) : s.prod⁻¹ = (s.map (·⁻¹)).prod :=
  neg_sum (α := AddOfMul α) _

def resp_sum
  [Zero α] [Add α] [IsAddCommMagma α] [IsAddSemigroup α]
  [Zero β] [Add β] [IsAddCommMagma β] [IsAddSemigroup β]
  [FunLike F α β] [IsZeroHom F α β] [IsAddHom F α β] (f: F) (s: Multiset α) : f s.sum = (s.map f).sum := by
  induction s with
  | nil => simp [resp_zero]
  | cons _ _ ih => simp [resp_add, ih]

def resp_mul
  [One α] [Mul α] [IsCommMagma α] [IsSemigroup α]
  [One β] [Mul β] [IsCommMagma β] [IsSemigroup β]
  [FunLike F α β] [IsOneHom F α β] [IsMulHom F α β] (f: F) (s: Multiset α) : f s.prod = (s.map f).prod :=
  resp_sum (α := AddOfMul α) (β := AddOfMul β) _ _

def smul_sum
  [SemiringOps α] [AddMonoidOps β] [IsSemiring α] [IsAddMonoid β] [IsAddCommMagma β]
  [SMul α β] [IsModule α β] (s: Multiset β) (x: α) : x • s.sum = (s.map (x • ·)).sum := by
  let f: AddGroupHom β β := {
    toFun := (x • ·)
    resp_zero' := ?_
    resp_add' := ?_
  }
  apply resp_sum f
  apply smul_zero
  apply smul_add

def mul_sum
  [Zero α] [Add α] [Mul α] [IsMulZeroClass α] [IsLeftDistrib α]
  [IsAddSemigroup α] [IsAddCommMagma α]
  (s: Multiset α) (x: α) : x * s.sum = (s.map (x * ·)).sum := by
  let f: AddGroupHom α α := {
    toFun := (x * ·)
    resp_zero' := ?_
    resp_add' := ?_
  }
  apply resp_sum f
  apply mul_zero
  apply mul_add

def sum_mul
  [Zero α] [Add α] [Mul α] [IsMulZeroClass α] [IsRightDistrib α]
  [IsAddSemigroup α] [IsAddCommMagma α]
  (s: Multiset α) (x: α) : s.sum * x = (s.map (· * x)).sum := by
  let f: AddGroupHom α α := {
    toFun := (· * x)
    resp_zero' := ?_
    resp_add' := ?_
  }
  apply resp_sum f
  apply zero_mul
  intros; apply add_mul

def sum_replicate [AddMonoidOps α] [IsAddCommMagma α] [IsAddMonoid α] (n: ℕ) (a: α) :
  sum (replicate n a) = n • a := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, succ_nsmul']

def prod_replicate [MonoidOps α] [IsCommMagma α] [IsMonoid α] (n: ℕ) (a: α) :
  prod (replicate n a) = a ^ n := sum_replicate (α := AddOfMul α) _ _

@[simp] def sum_singleton [Zero α] [Add α] [IsAddCommMagma α] [IsAddSemigroup α] [IsAddZeroClass α] (a: α) : sum {a} = a := by
  simp [singleton]
@[simp] def prod_singleton [One α] [Mul α] [IsCommMagma α] [IsSemigroup α] [IsMulOneClass α] (a: α) : prod {a} = a := by
  simp [singleton]

def sum_pairwise [Zero α] [Add α] [IsAddCommMagma α] [IsAddSemigroup α] [IsAddZeroClass α] (as: Multiset ι) (f g: ι -> α) :
  (as.map f).sum + (as.map g).sum = (as.map (fun i => f i + g i)).sum := by
  induction as with
  | nil => simp
  | cons a as ih =>
    simp [←ih]
    ac_rfl

def sum_comm
  [AddMonoidOps γ] [IsAddMonoid γ] [IsAddCommMagma γ]
  (as: Multiset α) (bs: Multiset β) (f: α -> β -> γ) :
  (as.map (fun a => (bs.map (fun b => f a b)).sum)).sum =
  (bs.map (fun b => (as.map (fun a => f a b)).sum)).sum := by
  induction as with
  | nil =>
    show 0 = _
    rw [sum_eq_zero]
    intro i eq
    rw [mem_map] at eq
    obtain ⟨b, h, rfl⟩ := eq
    rfl
  | cons a as ih =>
    simp
    rw [←sum_pairwise, ih]

end Multiset
