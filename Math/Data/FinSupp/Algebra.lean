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

def sum_eq_support_sum
   [Zero α] [∀a: α, Decidable (a = 0)] [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ] (f: Finsupp ι α S) (g: ι -> α -> γ) (resp: ∀i: ι, f i = 0 -> g i (f i) = 0):
   f.sum g resp = (f.support.val.map (fun i => g i (f i))).sum := by
   cases f with | mk f spec =>
   induction spec with | mk spec =>
   unfold sum
   show Multiset.sum _ = _
   dsimp [DFunLike.coe]
   obtain ⟨rest, disjoint, eq⟩ := Finsupp.eq_support_union ⟨f, Trunc.mk spec⟩ spec.val spec.property
   rw [eq]
   rw [Finset.union_disjoint,Multiset.map_append, Multiset.sum_append]
   conv => { rhs; rw [←add_zero (Multiset.sum _)] }
   congr
   rw [Multiset.sum_eq_zero]
   intro x h
   rw [Multiset.mem_map] at h
   obtain ⟨i, mem_rest, rfl⟩ := h
   have : f i = 0 := Classical.not_not.mp <| Iff.not_iff_not (Finsupp.mem_support (f := ⟨f, Trunc.mk spec⟩) (x := i)) |>.mp (disjoint _ · mem_rest)
   exact resp _ this

def sum_eq_support_sup_sum
   [Zero α] [∀a: α, Decidable (a = 0)] [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ] (f: Finsupp ι α S) (g: ι -> α -> γ) (resp: ∀i: ι, f i = 0 -> g i (f i) = 0)
   (s: Finset ι) (h: f.support ⊆ s):
   f.sum g resp = (s.val.map (fun i => g i (f i))).sum := by
   rw [sum_eq_support_sum]
   classical
   obtain ⟨s, hs, rfl⟩ := Finset.exists_union_eq_of_sub h
   rw [Finset.union_disjoint, Multiset.map_append, Multiset.sum_append]
   conv => { lhs; rw [←add_zero (Multiset.sum _)] }
   congr
   rw [Multiset.sum_eq_zero]
   intro x hx
   rw [Multiset.mem_map] at hx
   obtain ⟨i, mem, rfl⟩ := hx
   apply resp
   exact Classical.not_not.mp ((Iff.not_iff_not f.mem_support).mp (hs i · mem))

def add_sum
  [Zero α] [Add α] [IsAddZeroClass α]
  [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ]
  (f₀ f₁: Finsupp ι α S) (g: ι -> α -> γ)
  (resp_add: ∀i a b, g i (a + b) = g i a + g i b)
  (eq₀: ∀i, f₀ i = 0 -> g i (f₀ i) = 0)
  (eq₁: ∀i, f₁ i = 0 -> g i (f₁ i) = 0)
  (eq₂: ∀i, f₀ i + f₁ i = 0 -> g i (f₀ i + f₁ i) = 0) :
  sum (f₀ + f₁) g eq₂ = sum f₀ g eq₀ + sum f₁ g eq₁ := by
  classical
  rw [sum_eq_support_sup_sum (f := f₀ + f₁) (h := Finsupp.support_add f₀ f₁),
    sum_eq_support_sup_sum (f := f₀) (h := Finset.sub_union_left f₀.support f₁.support),
    sum_eq_support_sup_sum (f := f₁) (h := Finset.sub_union_right f₀.support f₁.support)]
  rw [Multiset.sum_pairwise]
  congr; ext i
  apply resp_add

def add_sum'
  [Zero α] [Add α] [IsAddZeroClass α]
  [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ]
  (f: Finsupp ι α S) (g₀ g₁: ι -> α -> γ)
  (eq₀: ∀i, f i = 0 -> g₀ i (f i) = 0)
  (eq₁: ∀i, f i = 0 -> g₁ i (f i) = 0) :
  sum f g₀ eq₀ + sum f g₁ eq₁ = sum f (fun i a => g₀ i a + g₁ i a ) (by
    intro i feq
    dsimp
    rw [eq₀, eq₁, add_zero] <;> assumption) := by
  classical
  simp [sum_eq_support_sum]
  apply Multiset.sum_pairwise

def single_sum
  [DecidableEq ι]
  [Zero α] [Add α] [IsAddZeroClass α]
  [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ]
  (f: ι -> α -> γ) {h}:
  (single a b: Finsupp ι α S).sum f h = f a b := by
  classical
  rw [sum_eq_support_sup_sum (h := Finsupp.support_single)]
  simp; congr
  rw [Finsupp.single]
  show (if _ then _ else _) = b
  rw [if_pos rfl]

def sum_sum_index
  [Zero α] [Add α] [IsAddZeroClass α]
  [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ]
  [AddMonoidOps γ₁] [IsAddCommMagma γ₁] [IsAddMonoid γ₁]
  (f: Finsupp ι α S) (g₀: ι -> α -> Finsupp ι γ S) (g₁: ι -> γ -> γ₁)
  {h₀: ∀i, g₀ i 0 = 0}
  {h₁: ∀i, g₁ i 0 = 0}:
  (f.sum g₀ (by intro i eq; rw [eq, h₀])).sum g₁ (by
    intro i eq; rw [eq]
    apply h₁) = f.sum (fun a b => (g₀ a b).sum g₁ (by intro i eq; rw [eq, h₁])) (by
    intro i eq; rw [eq]
    dsimp
    rw [sum_eq_zero]
    intro i
    rw [h₀]
    apply h₁) := by
    sorry

end Finsupp
