import Math.Data.Multiset.Algebra
import Math.Data.Fintype.Impls.LazyFinset
import Math.Data.Fintype.Algebra.Monoid
import Math.Data.DFinsupp.Defs

namespace DFinsupp

variable {α: ι -> Type*} [FiniteSupport S ι] [DecidableEq ι]

def sum [∀i, Zero (α i)] [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ] (f: DFinsupp α S) (g: ∀i, α i -> γ) (resp: ∀i: ι, f i = 0 -> g i (f i) = 0) : γ := by
  refine f.spec.lift (?_) ?_
  intro ⟨fs, hf⟩
  let fs : LazyFinset ι := fs
  exact (fs.toMultiset.map (fun a => g a (f a))).sum
  intro ⟨a, ha⟩ ⟨b, hb⟩
  dsimp
  classical
  obtain ⟨a', ha', eqa'⟩ := DFinsupp.eq_support_union f a ha
  obtain ⟨b', hb', eqb'⟩ := DFinsupp.eq_support_union f b hb
  rw [eqa', eqb']
  rw [LazyFinset.append_disjoint_toMultiset, LazyFinset.append_disjoint_toMultiset]
  simp [Multiset.map_append]
  rw [Multiset.sum_append]
  rw [Multiset.sum_append]
  congr 1
  rw [Multiset.sum_eq_zero, Multiset.sum_eq_zero]
  · intro o h
    rw [Multiset.mem_map] at h
    obtain ⟨i, i_mem, eq⟩ := h
    simp at i_mem
    have := Classical.not_not.mp <| (Iff.not_iff_not (DFinsupp.mem_support (f := f) (x := i))).mp (hb' i · i_mem)
    rw [resp _ this] at eq
    symm; assumption
  · intro o h
    rw [Multiset.mem_map] at h
    obtain ⟨i, i_mem, eq⟩ := h
    simp at i_mem
    have := Classical.not_not.mp <| (Iff.not_iff_not (DFinsupp.mem_support (f := f) (x := i))).mp (ha' i · i_mem)
    rw [resp _ this] at eq
    symm; assumption
  · assumption
  · assumption

def sum_rw_proof [∀i, Zero (α i)] [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ] (f: DFinsupp α S) (g: ∀i, α i -> γ) (resp₀ resp₁: ∀i: ι, f i = 0 -> g i (f i) = 0) :
  f.sum g resp₀ = f.sum g resp₁ := rfl

def prod [∀i, Zero (α i)] [MonoidOps γ] [IsCommMagma γ] [IsMonoid γ] (f: DFinsupp α S) (g: ∀i, α i -> γ) (resp: ∀i: ι, f i = 0 -> g i (f i) = 1) : γ :=
  sum (γ := AddOfMul γ) f g resp

def sum_eq_zero
  [∀i, Zero (α i)] [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ] (f: DFinsupp α S) (g: ∀i, α i -> γ) (eq: ∀i, g i (f i) = 0) :
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
  [∀i, Zero (α i)] [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ]
  (g: ∀i, α i -> γ) (eq: ∀i, (0: DFinsupp α S) i = 0 -> g i ((0: DFinsupp α S) i) = 0) : sum 0 g eq = 0 := by
  rw [sum_eq_zero]
  intro i
  rw [eq]
  rfl

def zero_prod
  [∀i, Zero (α i)] [MonoidOps γ] [IsCommMagma γ] [IsMonoid γ]
  (g: ∀i, α i -> γ) (eq: ∀i, (0: DFinsupp α S) i = 0 -> g i ((0: DFinsupp α S) i) = 1) : prod 0 g eq = 1 :=
  zero_sum (γ := AddOfMul γ) _ _

def coe_def [∀i, Zero (α i)] (f: DFinsupp α S) (i: ι) : f i = f.toFun i := rfl

def sum_eq_support_sum [∀i, Zero (α i)] [∀i, ∀a: α i, Decidable (a = 0)] [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ] (f: DFinsupp α S) (g: ∀i, α i -> γ) (resp: ∀i: ι, f i = 0 -> g i (f i) = 0): f.sum g resp = (f.support.toMultiset.map (fun i => g i (f i))).sum := by
    cases f with | mk f spec =>
    induction spec with | mk spec =>
    unfold sum
    show Multiset.sum _ = _
    dsimp [DFunLike.coe]
    obtain ⟨rest, disjoint, eq⟩ := DFinsupp.eq_support_union ⟨f, Trunc.mk spec⟩ spec.val spec.property
    rw [eq]
    obtain ⟨a, ha⟩ := spec
    dsimp
    classical
    rw [LazyFinset.append_disjoint_toMultiset]
    simp [Multiset.map_append]
    rw [Multiset.sum_append]
    conv => { rhs; rw [←add_zero (Multiset.sum _)] }
    congr
    rw [Multiset.sum_eq_zero]
    intro x h
    rw [Multiset.mem_map] at h
    obtain ⟨i, mem_rest, rfl⟩ := h
    apply resp
    -- show f i = 0
    apply Classical.byContradiction
    intro h
    have := disjoint i
    rw [DFinsupp.mem_support] at this
    replace h := this h
    simp at mem_rest
    contradiction
    assumption

def sum_eq_support_max_sum
   [∀i, Zero (α i)] [∀i, ∀a: α i, Decidable (a = 0)] [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ] (f: DFinsupp α S) (g: ∀i, α i -> γ) (resp: ∀i: ι, f i = 0 -> g i (f i) = 0)
   (s: LazyFinset ι) (h: f.support ⊆ s):
   f.sum g resp = (s.toMultiset.map (fun i => g i (f i))).sum := by
   rw [sum_eq_support_sum]
   classical
   obtain ⟨s, rfl, hs⟩ := LazyFinset.exists_append_eq_of_sub h
   rw [LazyFinset.append_disjoint_toMultiset, Multiset.map_append, Multiset.sum_append]
   conv => { lhs; rw [←add_zero (Multiset.sum _)] }
   congr
   rw [Multiset.sum_eq_zero]
   intro x hx
   rw [Multiset.mem_map] at hx
   obtain ⟨i, mem, rfl⟩ := hx
   simp at mem
   apply resp
   exact Classical.not_not.mp ((Iff.not_iff_not f.mem_support).mp (hs i · mem))
   assumption

def add_sum
  [∀i, Zero (α i)] [∀i, Add (α i)] [∀i, IsAddZeroClass (α i)]
  [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ]
  (f₀ f₁: DFinsupp α S) (g: ∀i, α i -> γ)
  (map_add: ∀i a b, g i (a + b) = g i a + g i b)
  (eq₀: ∀i, f₀ i = 0 -> g i (f₀ i) = 0)
  (eq₁: ∀i, f₁ i = 0 -> g i (f₁ i) = 0)
  (eq₂: ∀i, f₀ i + f₁ i = 0 -> g i (f₀ i + f₁ i) = 0) :
  sum (f₀ + f₁) g eq₂ = sum f₀ g eq₀ + sum f₁ g eq₁ := by
  classical
  rw [sum_eq_support_max_sum (f := f₀ + f₁) (h := DFinsupp.support_add f₀ f₁),
    sum_eq_support_max_sum (f := f₀) (h := LazyFinset.sub_append_left f₀.support f₁.support),
    sum_eq_support_max_sum (f := f₁) (h := LazyFinset.sub_append_right f₀.support f₁.support)]
  rw [Multiset.sum_pairwise]
  congr; ext i
  apply map_add

def add_prod
  [∀i, Zero (α i)] [∀i, Add (α i)] [∀i, IsAddZeroClass (α i)]
  [MonoidOps γ] [IsCommMagma γ] [IsMonoid γ]
  (f₀ f₁: DFinsupp α S) (g: ∀i, α i -> γ)
  (map_add: ∀i a b, g i (a + b) = g i a * g i b)
  (eq₀: ∀i, f₀ i = 0 -> g i (f₀ i) = 1)
  (eq₁: ∀i, f₁ i = 0 -> g i (f₁ i) = 1)
  (eq₂: ∀i, f₀ i + f₁ i = 0 -> g i (f₀ i + f₁ i) = 1) :
  prod (f₀ + f₁) g eq₂ = prod f₀ g eq₀ * prod f₁ g eq₁ :=
  add_sum (γ := AddOfMul γ) _ _ _ map_add _ _ _

def add_sum'
  [∀i, Zero (α i)] [∀i, Add (α i)] [∀i, IsAddZeroClass (α i)]
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
  [∀i, Zero (α i)] [∀i, Add (α i)] [∀i, IsAddZeroClass (α i)]
  [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ]
  (f: ∀i, α i -> γ) {h}:
  (single a b: DFinsupp α S).sum f h = f a b := by
  classical
  rw [sum_eq_support_max_sum (h := DFinsupp.support_single)]
  simp

def single_prod
  [∀i, Zero (α i)] [∀i, Add (α i)] [∀i, IsAddZeroClass (α i)]
  [MonoidOps γ] [IsCommMagma γ] [IsMonoid γ]
  (f: ∀i, α i -> γ) {h}:
  (single a b: DFinsupp α S).prod f h = f a b :=
  single_sum (γ := AddOfMul γ) _

def map_sum
  [∀i, Zero (α i)] [∀i, Add (α i)] [∀i, IsAddZeroClass (α i)]
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

def sum_single [∀i, AddMonoidOps (α i)] [∀i, IsAddMonoid (α i)] [∀i, IsAddCommMagma (α i)]
  (f: DFinsupp α S) : f.sum single (by
    intro i eq
    rw [eq]; ext i ; rw [apply_single]; split <;> (try subst i; rfl); rfl) = f := by
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
    have : i ∈ f.support.toMultiset := by simpa [mem_support]
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
    have : (i₀::ₘas).Nodup := by rw [←eq]; apply f.support.toMultiset_nodup
    have := this.head
    contradiction

private def sum' [∀i, Zero (α i)] [∀i, ∀a: α i, Decidable (a = 0)] [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ] (f: DFinsupp α S) (g: ∀i, α i -> γ) :=
  (f.support.toMultiset.map (fun i => g i (f i))).sum

private def sum_eq_sum'
   [∀i, Zero (α i)] [∀i, ∀a: α i, Decidable (a = 0)] [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ] (f: DFinsupp α S) (g: ∀i, α i -> γ) (resp: ∀i: ι, f i = 0 -> g i (f i) = 0):
   f.sum g resp = f.sum' g := by
   rw [sum', sum_eq_support_sum]

def sum_pairwise
   [∀i, Zero (α i)] [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ] (f: DFinsupp α S)
   (g₀: ∀i, α i -> γ) (resp₀: ∀i: ι, f i = 0 -> g₀ i (f i) = 0)
   (g₁: ∀i, α i -> γ) (resp₁: ∀i: ι, f i = 0 -> g₁ i (f i) = 0) :
   f.sum g₀ resp₀ + f.sum g₁ resp₁ = f.sum (fun i a => g₀ i a + g₁ i a) (by
    intro i eq
    dsimp; rw [resp₀ _ eq, resp₁ _ eq, add_zero]) := by
  classical
  simp [sum_eq_support_sum]
  apply Multiset.sum_pairwise

end DFinsupp
