import Math.Algebra.Semiring.Defs
import Math.Data.Fintype.Defs
import Math.Data.Fintype.Prod

def List.prod [Mul α] [One α] : List α -> α := List.sum (α := AddOfMul α)

def Fintype.sum [ft: Fintype ι] [Add α] [Zero α] (f: ι -> α) := (ft.all.map f).sum
def Fintype.prod [ft: Fintype ι] [Mul α] [One α] (f: ι -> α) := (ft.all.map f).prod

namespace List

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

end List

namespace Fintype

def sum_of_equiv
  {f₀: Fintype ι₀} {f₁: Fintype ι₁}
  [Add α] [Zero α] [IsAddSemigroup α]
  [IsAddZeroClass α] [IsAddCommMagma α]
  (eqv: ι₁ ≃ ι₀) (f: ι₀ -> α) :
  sum f = sum (fun i => f (eqv i)) := by
  unfold sum
  cases f₀ with | mk f₀ nodup₀ complete₀ =>
  cases f₁ with | mk f₁ nodup₁ complete₁ =>
  dsimp
  have mem_iff : ∀x, eqv x ∈ f₀ ↔ x ∈ f₁ := by
    intro x
    apply Iff.intro <;> intro
    apply complete₁
    apply complete₀
  clear complete₀ complete₁
  induction nodup₀ generalizing f₁ with
  | nil =>
    cases f₁
    rfl
    have := (mem_iff _).mpr (List.Mem.head _)
    contradiction
  | cons head_not_in_tail tail_nodup ih =>
    rename_i a as
    have mem := (mem_iff (eqv.symm a)).mp (by
      rw [Equiv.symm_coe]
      simp)
    have ⟨bs₀, bs₁, eq⟩ := List.mem_iff_append.mp mem
    subst eq
    clear mem
    rw [List.map_append, List.map_cons, List.map_cons,
      List.sum_extract, List.sum_cons, ih (bs₀ ++ bs₁)]
    congr
    rw [Equiv.symm_coe]
    rw [List.map_append]
    refine List.Sublist.nodup ?_ nodup₁
    simp
    intro x
    apply Iff.intro
    · intro hx
      have := (mem_iff _).mp (List.Mem.tail _ hx)
      simp at this
      rcases this with h | h | h
      simp [h]
      subst x
      rw [Equiv.symm_coe] at hx
      have := head_not_in_tail _ hx
      contradiction
      simp [h]
    · intro hx
      simp at hx
      simp at mem_iff
      rcases hx with h | h
      apply ((mem_iff x).mpr (by simp [h])).resolve_left
      rintro rfl
      have := List.minCount_of_nodup _ nodup₁ (n := 2) (x := x) ?_
      contradiction
      apply List.MinCount.append (n := 1) (m := 1)
      apply List.mem_iff_MinCount_one.mp
      assumption
      rw [Equiv.coe_symm]
      apply List.MinCount.head
      apply List.MinCount.zero
      apply ((mem_iff x).mpr (by simp [h])).resolve_left
      rintro rfl
      have := List.minCount_of_nodup _ nodup₁ (n := 2) (x := x) ?_
      contradiction
      apply List.MinCount.append (n := 0) (m := 2)
      apply List.MinCount.zero
      rw [Equiv.coe_symm]
      apply List.MinCount.head
      apply List.mem_iff_MinCount_one.mp
      assumption

def prod_of_equiv
  {f₀: Fintype ι₀} {f₁: Fintype ι₁}
  [Mul α] [One α] [IsSemigroup α]
  [IsMulOneClass α] [IsCommMagma α]
  (eqv: ι₁ ≃ ι₀) (f: ι₀ -> α) :
  prod f = prod (fun i => f (eqv i)) :=
  sum_of_equiv (α := AddOfMul α) eqv f

-- prove that the value of the sum is independent of the ordering
-- of the values, given that `α` is a commutative additve monoid
-- altough we don't require that all monoid ops are implemented
-- so we don't require `IsAddMonoid`
def sum_eq {f₀: Fintype ι} {f₁: Fintype ι}
  [Add α] [Zero α] [IsAddSemigroup α]
  [IsAddZeroClass α] [IsAddCommMagma α]
  (f: ι -> α) :
  @Fintype.sum ι α f₀ _ _ f  = @Fintype.sum ι α f₁ _ _ f := by
  apply sum_of_equiv Equiv.refl

-- prove that the value of the sum is independent of the ordering
-- of the values, given that `α` is a commutative monoid
-- altough we don't require that all monoid ops are implemented
-- so we don't require `IsMonoid`
def prod_eq {f₀: Fintype ι} {f₁: Fintype ι}
  [Mul α] [One α] [IsSemigroup α]
  [IsMulOneClass α] [IsCommMagma α]
  (f: ι -> α) :
  @Fintype.prod ι α f₀ _ _ f  = @Fintype.prod ι α f₁ _ _ f :=
  sum_eq (α := AddOfMul α) f

def sum_mul
  [f₀: Fintype ι] [Zero α] [Add α] [Mul α] [IsMulZeroClass α] [IsRightDistrib α]
  (f: ι -> α) (k: α) :
  sum f * k = sum (fun i => f i * k) := by
  cases f₀ with
  | mk all nodup complete =>
  dsimp [sum]
  clear complete nodup
  induction all with
  | nil => apply zero_mul
  | cons a as ih =>
    dsimp
    rw [add_mul, ih]

def mul_sum
  [f₀: Fintype ι] [Zero α] [Add α] [Mul α] [IsMulZeroClass α] [IsLeftDistrib α]
  (f: ι -> α) (k: α) :
  k * sum f = sum (fun i => k * f i) := by
  cases f₀ with
  | mk all nodup complete =>
  dsimp [sum]
  clear complete nodup
  induction all with
  | nil => apply mul_zero
  | cons a as ih =>
    dsimp
    rw [mul_add, ih]

def sum_sum [f₀: Fintype ι₀] [f₁: Fintype ι₁]
  [Zero α] [Add α] [IsAddZeroClass α] [IsAddSemigroup α]
  (f: ι₀ -> ι₁ -> α):
    (sum fun i₀ => sum fun i₁ => f i₀ i₁) = sum fun i: ι₀ × ι₁ => f i.1 i.2 := by
    cases f₀ with | mk f₀ nodup₀ complete₀ =>
    cases f₁ with | mk f₁ nodup₁ complete₁ =>
    dsimp [sum]
    unfold Fintype.all instFintypeProd Fintype.ofEquiv Fintype.all
      instFintypeSigma Prod.equivSigma
    dsimp
    clear complete₀ complete₁ nodup₀ nodup₁
    simp [Function.comp_def, List.map_flatMap]
    induction f₀ with
    | nil => rfl
    | cons a as ih => simp [ih, List.sum_append]

def prod_prod [f₀: Fintype ι₀] [f₁: Fintype ι₁]
  [One α] [Mul α] [IsMulOneClass α] [IsSemigroup α]
  (f: ι₀ -> ι₁ -> α):
  (prod (α := α) fun i₀ => prod fun i₁ => f i₀ i₁) = prod fun i: ι₀ × ι₁ => f i.1 i.2 :=
  sum_sum (α := AddOfMul α) f

def sum_add
  [fι: Fintype ι]
  [Add α] [Zero α] [IsAddCommMagma α] [IsAddZeroClass α] [IsAddSemigroup α]
  (f g: ι -> α) : Fintype.sum f + Fintype.sum g = Fintype.sum (fun i => f i + g i) := by
  cases fι with | mk as nodup complete =>
  simp [sum]
  clear nodup complete
  induction as with
  | nil => apply zero_add
  | cons a as ih =>
    simp
    rw [show
      f a + (List.map f as).sum + (g a + (List.map g as).sum) =
      f a + g a + ((List.map f as).sum + (List.map g as).sum) by ac_rfl, ih]

def prod_mul
  [fι: Fintype ι]
  [Mul α] [One α] [IsCommMagma α] [IsMulOneClass α] [IsSemigroup α]
  (f g: ι -> α) : Fintype.prod f * Fintype.prod g = Fintype.prod (fun i => f i * g i) :=
  sum_add (α := AddOfMul α) f g

end Fintype
