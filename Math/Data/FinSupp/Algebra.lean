import Math.Data.Multiset.Algebra
import Math.Data.FinSupp.Defs

namespace Finsupp

variable [FiniteSupportSet S ι]

def sum [Zero α] [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ] (f: Finsupp ι α S) (g: ι -> α -> γ) (resp: ∀i: ι, f i = 0 -> g i (f i) = 0) : γ := by
  refine f.spec.lift (?_) ?_
  intro ⟨fs, hf⟩
  let _ : FinsetLike S ι := inferInstance
  let fs : Finset ι := fs
  exact (fs.val.map (fun a => g a (f a))).sum
  intro ⟨a, ha⟩ ⟨b, hb⟩
  dsimp
  classical
  obtain ⟨a', ha', eqa'⟩ := Finsupp.eq_support_union f a ha
  obtain ⟨b', hb', eqb'⟩ := Finsupp.eq_support_union f b hb
  rw [eqa', eqb']
  unfold Finset.union_disjoint
  simp [Multiset.map_append]
  rw [Multiset.sum_append]
  rw [Multiset.sum_append]
  congr 1
  rw [Multiset.sum_eq_zero, Multiset.sum_eq_zero]
  intro o h
  rw [Multiset.mem_map] at h
  obtain ⟨i, i_mem, eq⟩ := h
  have := Classical.not_not.mp <| (Iff.not_iff_not (Finsupp.mem_support (f := f) (x := i))).mp (hb' i · i_mem)
  rw [resp _ this] at eq
  symm; assumption
  intro o h
  rw [Multiset.mem_map] at h
  obtain ⟨i, i_mem, eq⟩ := h
  have := Classical.not_not.mp <| (Iff.not_iff_not (Finsupp.mem_support (f := f) (x := i))).mp (ha' i · i_mem)
  rw [resp _ this] at eq
  symm; assumption

def prod [Zero α] [MonoidOps γ] [IsCommMagma γ] [IsMonoid γ] (f: Finsupp ι α S) (g: ι -> α -> γ) (resp: ∀i: ι, f i = 0 -> g i (f i) = 1) : γ :=
  sum (γ := AddOfMul γ) f g resp

def sum_eq_zero
  [Zero α] [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ] (f: Finsupp ι α S) (g: ι -> α -> γ) (eq: ∀i, g i (f i) = 0) :
  f.sum g (by intro i _; rw [eq]) = 0 := by
  cases f with | mk f spec =>
  induction spec with | mk spec =>
  obtain ⟨s, spec⟩ := spec
  apply Multiset.sum_eq_zero
  intro o h
  rw [Multiset.mem_map] at h
  obtain ⟨i, _, rfl⟩ := h
  rw [eq]

def zero_sum
  [Zero α] [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ]
  (g: ι -> α -> γ) (eq: ∀i, (0: Finsupp ι α S) i = 0 -> g i ((0: Finsupp ι α S) i) = 0) : sum 0 g eq = 0 := by
  rw [sum_eq_zero]
  intro i
  rw [eq]
  rfl

def coe_def [Zero α] (f: Finsupp ι α S) (i: ι) : f i = f.toFun i := rfl

def add_sum
  [Zero α] [Add α] [IsAddZeroClass α]
  [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ]
  (f₀ f₁: Finsupp ι α S) (g: ι -> α -> γ)
  (resp_add: ∀i a b, g i (a + b) = g i a + g i b)
  (eq₀: ∀i, f₀ i = 0 -> g i (f₀ i) = 0)
  (eq₁: ∀i, f₁ i = 0 -> g i (f₁ i) = 0)
  (eq₂: ∀i, f₀ i + f₁ i = 0 -> g i (f₀ i + f₁ i) = 0) :
  sum (f₀ + f₁) g eq₂ = sum f₀ g eq₀ + sum f₁ g eq₁ := by
  cases f₀ with | mk f₀ spec₀ =>
  cases f₁ with | mk f₁ spec₁ =>
  induction spec₀ with | mk spec₀ =>
  induction spec₁ with | mk spec₁ =>
  show Multiset.sum _ = Multiset.sum _ + Multiset.sum _
  rw [←Multiset.sum_append]
  simp; simp [coe_def]
  sorry

end Finsupp
