import Math.Data.DFinsupp.Defs
import Math.Algebra.Ring.Defs
import Math.Data.Multiset.Algebra

namespace DFinsupp

variable {α : ι -> Type*} [FiniteSupport S ι]

section

variable [∀i, Zero (α i)]

def sum [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ] (f: DFinsupp α S) (g: ∀i, α i -> γ) (resp: ∀i: ι, f i = 0 -> g i (f i) = 0) : γ := by
  refine f.spec.lift (?_) ?_
  intro ⟨fs, hf⟩
  let _ : FinsetLike S ι := inferInstance
  let fs : Finset ι := fs
  exact (fs.val.map (fun a => g a (f a))).sum
  intro ⟨a, ha⟩ ⟨b, hb⟩
  dsimp
  classical
  obtain ⟨a', ha', eqa'⟩ := DFinsupp.eq_support_union f a ha
  obtain ⟨b', hb', eqb'⟩ := DFinsupp.eq_support_union f b hb
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
  have := Classical.not_not.mp <| (Iff.not_iff_not (DFinsupp.mem_support (f := f) (x := i))).mp (hb' i · i_mem)
  rw [resp _ this] at eq
  symm; assumption
  intro o h
  rw [Multiset.mem_map] at h
  obtain ⟨i, i_mem, eq⟩ := h
  have := Classical.not_not.mp <| (Iff.not_iff_not (DFinsupp.mem_support (f := f) (x := i))).mp (ha' i · i_mem)
  rw [resp _ this] at eq
  symm; assumption

variable [∀i (a: α i), Decidable (a = 0)]

def sum_eq_support_sum [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ] (f: DFinsupp α S) (g: ∀i, α i -> γ) (resp: ∀i: ι, f i = 0 -> g i (f i) = 0):
   f.sum g resp = (f.support.val.map (fun i => g i (f i))).sum := by
   classical
   cases f with | mk f spec =>
   induction spec with | mk spec =>
   unfold sum
   show Multiset.sum _ = _
   dsimp [DFunLike.coe]
   obtain ⟨rest, disjoint, eq⟩ := DFinsupp.eq_support_union ⟨f, Trunc.mk spec⟩ spec.val spec.property
   rw [eq]
   rw [Finset.union_disjoint,Multiset.map_append, Multiset.sum_append]
   conv => { rhs; rw [←add_zero (Multiset.sum _)] }
   congr
   rw [Multiset.sum_eq_zero]
   intro x h
   rw [Multiset.mem_map] at h
   obtain ⟨i, mem_rest, rfl⟩ := h
   have : f i = 0 := Classical.not_not.mp <| Iff.not_iff_not (DFinsupp.mem_support (f := ⟨f, Trunc.mk spec⟩) (x := i)) |>.mp (disjoint _ · mem_rest)
   exact resp _ this

def sum_eq_support_sup_sum [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ] (f: DFinsupp α S) (g: ∀i, α i -> γ) (resp: ∀i: ι, f i = 0 -> g i (f i) = 0)
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

def sum_eq_zero [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ] (f: DFinsupp α S) (g: ∀i, α i -> γ) (eq: ∀i, g i (f i) = 0) :
  f.sum g (by intro i _; rw [eq]) = 0 := by
  cases f with | mk f spec =>
  induction spec with | mk spec =>
  obtain ⟨s, spec⟩ := spec
  apply Multiset.sum_eq_zero
  intro o h
  rw [Multiset.mem_map] at h
  obtain ⟨i, _, rfl⟩ := h
  rw [eq]

def zero_sum [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ]
  (g: ∀i, α i -> γ) (eq: ∀i, (0: DFinsupp α S) i = 0 -> g i ((0: DFinsupp α S) i) = 0) : sum 0 g eq = 0 := by
  rw [sum_eq_zero]
  intro i
  rw [eq]
  rfl

def add_sum [∀i, Add (α i)] [∀i, IsAddZeroClass (α i)] [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ]
  (f₀ f₁: DFinsupp α S) (g: ∀i, α i -> γ)
  (map_add: ∀i a b, g i (a + b) = g i a + g i b)
  (eq₀: ∀i, f₀ i = 0 -> g i (f₀ i) = 0)
  (eq₁: ∀i, f₁ i = 0 -> g i (f₁ i) = 0)
  (eq₂: ∀i, f₀ i + f₁ i = 0 -> g i (f₀ i + f₁ i) = 0) :
  sum (f₀ + f₁) g eq₂ = sum f₀ g eq₀ + sum f₁ g eq₁ := by
  classical
  rw [sum_eq_support_sup_sum (f := f₀ + f₁) (h := DFinsupp.support_add f₀ f₁),
    sum_eq_support_sup_sum (f := f₀) (h := Finset.sub_union_left f₀.support f₁.support),
    sum_eq_support_sup_sum (f := f₁) (h := Finset.sub_union_right f₀.support f₁.support)]
  rw [Multiset.sum_pairwise]
  congr; ext i
  apply map_add

def sum_pairwise
  [∀i, Add (α i)] [∀i, IsAddZeroClass (α i)]
  [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ]
  (f: DFinsupp α S) (g₀ g₁: ∀i, α i -> γ)
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
  [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ]
  (f: ∀i, α i -> γ) {h}:
  (single a b: DFinsupp α S).sum f h = f a b := by
  classical
  rw [sum_eq_support_sup_sum (h := DFinsupp.support_single)]
  simp

def map_sum
  [∀i, Add (α i)] [∀i, IsAddZeroClass (α i)]
  [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ]
  [AddMonoidOps γ'] [IsAddCommMagma γ'] [IsAddMonoid γ']
  [FunLike F γ γ'] [IsZeroHom F γ γ'] [IsAddHom F γ γ']
  (f: DFinsupp α S) (g: ∀i, α i -> γ) {h} (f₀: F) : f₀ (f.sum g h) = f.sum (fun i a => f₀ (g i a)) (by
    intro i eq
    dsimp
    rw [h _ eq, map_zero]) := by
    cases f with | mk f spec =>
    induction spec with | mk spec =>
    apply Eq.trans
    apply Multiset.map_sum
    rw [Multiset.map_map]
    rfl

end

def smul_sum
  [SemiringOps R] [IsSemiring R]
  [∀i, AddMonoidOps (α i)] [∀i, IsAddMonoid (α i)] [∀i, IsAddCommMagma (α i)]
  [∀i (a: α i), Decidable (a = 0)]
  [∀i, SMul R (α i)] [∀i, IsModule R (α i)]
  [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ]
  [SMul R γ] [IsModule R γ]
  (r: R)
  (f: DFinsupp α S) (g: ∀i, α i -> γ)
  (map_smul: ∀i a, g i (r • a) = r • g i a)
  (eq₀: ∀i, f i = 0 -> g i (f i) = 0)
  (eq₂: ∀i, r • f i = 0 -> g i (r • f i) = 0):
  sum (r • f) g eq₂ = r • sum f g eq₀ := by
  classical
  rw [sum_eq_support_sup_sum (h := f.support_smul r), sum_eq_support_sum]
  rw [
    Multiset.smul_sum, Multiset.map_map, Function.comp_def]
  congr; ext i
  apply map_smul

def sum_single [DecidableEq ι] [∀i, AddMonoidOps (α i)] [∀i, IsAddMonoid (α i)] [∀i, IsAddCommMagma (α i)]
  [∀i (a: α i), Decidable (a = 0)]
  (f: DFinsupp α S) : f.sum (single (S := S)) (by
    intro i eq
    rw [eq]; ext i ; rw [apply_single]; split; subst i; rfl; rfl) = f := by
    ext i
    let f' : DFinsupp α S →+ α i := {
      toFun x := x i
      map_zero := rfl
      map_add := rfl
    }
    show f' _ = _
    rw [map_sum]
    show f.sum (fun x a => single (S := S) x a i) _ = _
    by_cases h:f i = 0
    rw [sum_eq_zero, h]
    intro i'
    rw [apply_single]; split
    subst i; assumption; rfl
    classical
    rw [sum_eq_support_sum]
    have : i ∈ f.support.val := by
      apply mem_support.mpr
      assumption
    rw [Multiset.mem_spec] at this
    obtain ⟨as, eq⟩ := this
    rw [eq]
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.sum_eq_zero, add_zero, apply_single, dif_pos rfl]
    rfl
    intro i₀ h₀
    rw [Multiset.mem_map] at h₀
    obtain ⟨i₀, h₀, rfl⟩ := h₀
    rw [apply_single, dif_neg]
    rintro rfl
    have : (i₀::ₘas).Nodup := by rw [←eq]; apply f.support.property
    have := this.head
    contradiction

end DFinsupp
