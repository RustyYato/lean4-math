import Math.Data.Multiset.Algebra
import Math.Data.Fintype.Impls.LazyFinset
import Math.Data.Fintype.Algebra.Monoid
import Math.Data.Finsupp.Defs

namespace Finsupp

variable [FiniteSupport S ι] [DecidableEq ι]

def sum [Zero α] [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ] (f: Finsupp ι α S) (g: ι -> α -> γ) (resp: ∀i: ι, f i = 0 -> g i (f i) = 0) : γ := by
  refine f.spec.lift (?_) ?_
  intro ⟨fs, hf⟩
  let fs : LazyFinset ι := fs
  exact (fs.toMultiset.map (fun a => g a (f a))).sum
  intro ⟨a, ha⟩ ⟨b, hb⟩
  dsimp
  classical
  obtain ⟨a', ha', eqa'⟩ := Finsupp.eq_support_union f a ha
  obtain ⟨b', hb', eqb'⟩ := Finsupp.eq_support_union f b hb
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
    have := Classical.not_not.mp <| (Iff.not_iff_not (Finsupp.mem_support (f := f) (x := i))).mp (hb' i · i_mem)
    rw [resp _ this] at eq
    symm; assumption
  · intro o h
    rw [Multiset.mem_map] at h
    obtain ⟨i, i_mem, eq⟩ := h
    simp at i_mem
    have := Classical.not_not.mp <| (Iff.not_iff_not (Finsupp.mem_support (f := f) (x := i))).mp (ha' i · i_mem)
    rw [resp _ this] at eq
    symm; assumption
  · assumption
  · assumption

def sum_rw_proof [Zero α] [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ] (f: Finsupp ι α S) (g: ι -> α -> γ) (resp₀ resp₁: ∀i: ι, f i = 0 -> g i (f i) = 0) :
  f.sum g resp₀ = f.sum g resp₁ := rfl

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

def zero_prod
  [Zero α] [MonoidOps γ] [IsCommMagma γ] [IsMonoid γ]
  (g: ι -> α -> γ) (eq: ∀i, (0: Finsupp ι α S) i = 0 -> g i ((0: Finsupp ι α S) i) = 1) : prod 0 g eq = 1 :=
  zero_sum (γ := AddOfMul γ) _ _

def coe_def [Zero α] (f: Finsupp ι α S) (i: ι) : f i = f.toFun i := rfl

def sum_eq_support_sum [Zero α] [∀a: α, Decidable (a = 0)] [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ] (f: Finsupp ι α S) (g: ι -> α -> γ) (resp: ∀i: ι, f i = 0 -> g i (f i) = 0): f.sum g resp = (f.support.toMultiset.map (fun i => g i (f i))).sum := by
    cases f with | mk f spec =>
    induction spec with | mk spec =>
    unfold sum
    show Multiset.sum _ = _
    dsimp [DFunLike.coe]
    obtain ⟨rest, disjoint, eq⟩ := Finsupp.eq_support_union ⟨f, Trunc.mk spec⟩ spec.val spec.property
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
    rw [Finsupp.mem_support] at this
    replace h := this h
    simp at mem_rest
    contradiction
    assumption

def sum_eq_support_max_sum
   [Zero α] [∀a: α, Decidable (a = 0)] [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ] (f: Finsupp ι α S) (g: ι -> α -> γ) (resp: ∀i: ι, f i = 0 -> g i (f i) = 0)
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
  [Zero α] [Add α] [IsAddZeroClass α]
  [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ]
  (f₀ f₁: Finsupp ι α S) (g: ι -> α -> γ)
  (map_add: ∀i a b, g i (a + b) = g i a + g i b)
  (eq₀: ∀i, f₀ i = 0 -> g i (f₀ i) = 0)
  (eq₁: ∀i, f₁ i = 0 -> g i (f₁ i) = 0)
  (eq₂: ∀i, f₀ i + f₁ i = 0 -> g i (f₀ i + f₁ i) = 0) :
  sum (f₀ + f₁) g eq₂ = sum f₀ g eq₀ + sum f₁ g eq₁ := by
  classical
  rw [sum_eq_support_max_sum (f := f₀ + f₁) (h := Finsupp.support_add f₀ f₁),
    sum_eq_support_max_sum (f := f₀) (h := LazyFinset.sub_append_left f₀.support f₁.support),
    sum_eq_support_max_sum (f := f₁) (h := LazyFinset.sub_append_right f₀.support f₁.support)]
  rw [Multiset.sum_pairwise]
  congr; ext i
  apply map_add

def add_prod
  [Zero α] [Add α] [IsAddZeroClass α]
  [MonoidOps γ] [IsCommMagma γ] [IsMonoid γ]
  (f₀ f₁: Finsupp ι α S) (g: ι -> α -> γ)
  (map_add: ∀i a b, g i (a + b) = g i a * g i b)
  (eq₀: ∀i, f₀ i = 0 -> g i (f₀ i) = 1)
  (eq₁: ∀i, f₁ i = 0 -> g i (f₁ i) = 1)
  (eq₂: ∀i, f₀ i + f₁ i = 0 -> g i (f₀ i + f₁ i) = 1) :
  prod (f₀ + f₁) g eq₂ = prod f₀ g eq₀ * prod f₁ g eq₁ :=
  add_sum (γ := AddOfMul γ) _ _ _ map_add _ _ _

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

def smul_sum
  [SemiringOps α] [IsSemiring α]
  [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ]
  [SMul α γ] [IsModule α γ]
  (a₀: α)
  (f: Finsupp ι α S) (g: ι -> α -> γ)
  (map_smul: ∀i a, g i (a₀ * a) = a₀ • g i a)
  (eq₀: ∀i, f i = 0 -> g i (f i) = 0)
  (eq₂: ∀i, a₀ • f i = 0 -> g i (a₀ • f i) = 0):
  sum (a₀ • f) g eq₂ = a₀ • sum f g eq₀ := by
  classical
  rw [sum_eq_support_max_sum (h := f.support_smul a₀), sum_eq_support_sum]
  rw [Multiset.smul_sum, Multiset.map_map, Function.comp_def]
  congr; ext i
  apply map_smul

def single_sum
  [Zero α] [Add α] [IsAddZeroClass α]
  [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ]
  (f: ι -> α -> γ) {h}:
  (single a b: Finsupp ι α S).sum f h = f a b := by
  classical
  rw [sum_eq_support_max_sum (h := Finsupp.support_single)]
  simp; congr
  rw [Finsupp.single]
  show (if _ then _ else _) = b
  rw [if_pos rfl]

def single_prod
  [Zero α] [Add α] [IsAddZeroClass α]
  [MonoidOps γ] [IsCommMagma γ] [IsMonoid γ]
  (f: ι -> α -> γ) {h}:
  (single a b: Finsupp ι α S).prod f h = f a b :=
  single_sum (γ := AddOfMul γ) _

def map_sum
  [Zero α] [Add α] [IsAddZeroClass α]
  [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ]
  [AddMonoidOps γ'] [IsAddCommMagma γ'] [IsAddMonoid γ']
  [FunLike F γ γ'] [IsZeroHom F γ γ'] [IsAddHom F γ γ']
  (f: Finsupp ι α S) (g: ι -> α -> γ) {h} (f₀: F) : f₀ (f.sum g h) = f.sum (fun i a => f₀ (g i a)) (by
    intro i eq
    dsimp
    rw [h _ eq, map_zero]) := by
    cases f with | mk f spec =>
    induction spec with | mk spec =>
    apply Eq.trans
    apply Multiset.map_sum
    rw [Multiset.map_map]
    rfl

def sum_single [AddMonoidOps α] [IsAddMonoid α] [IsAddCommMagma α]
  (f: Finsupp ι α S) : f.sum single (by
    intro i eq
    rw [eq]; ext i ; rw [apply_single]; split <;> rfl) = f := by
    ext i
    let f' : Finsupp ι α S →+ α := {
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
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.sum_eq_zero, add_zero, apply_single, if_pos rfl]
    intro i₀ h₀
    rw [Multiset.mem_map] at h₀
    obtain ⟨i₀, h₀, rfl⟩ := h₀
    rw [apply_single, if_neg]
    rintro rfl
    have : (i::ₘas).Nodup := by rw [←eq]; apply f.support.toMultiset_nodup
    have := this.head
    contradiction

def sum_apply_single
  [Zero α] [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ]
  [FunLike F α γ] [IsZeroHom F α γ]
  (f: Finsupp ι α S) (g: F):
  f.sum (fun i a => Finsupp.single (S := S) (β := γ) i (g a) j) (by
    intro i eq
    dsimp; rw [eq, map_zero, apply_single]
    split <;> rfl) = g (f j) := by
  cases f with | mk f spec =>
  induction spec with | mk spec =>
  obtain ⟨supp, spec⟩ := spec
  show _ = g (f j)
  show Multiset.sum _ = _
  simp
  show (Multiset.map (fun i => single i (g (f i)) j) _).sum =_
  replace spec : ∀x: ι, f x ≠ 0 -> x ∈ (supp: LazyFinset _) := spec
  revert spec
  generalize (supp: LazyFinset ι) = supp'
  clear supp
  -- cases supp' with | mk supp nodup =>
  -- simp
  intro h
  replace h := h j
  induction supp' with
  | nil =>
    show 0 = _
    suffices f j = 0 by
      rw [this, map_zero]
    apply Classical.byContradiction
    intro h'
    have := h h'
    contradiction
  | cons i supp ne ih =>
    rw [LazyFinset.cons_toMultiset _ _ ne]
    simp; rw [apply_single]; split
    subst j
    rw [Multiset.sum_eq_zero, add_zero]
    intro x h'
    rw [Multiset.mem_map] at h'
    obtain ⟨i₀, h₀, rfl⟩ := h'
    rw [apply_single, if_neg]
    rintro rfl;
    simp at h₀
    contradiction
    rw [zero_add]
    apply ih
    intro g
    simp [g] at h
    rcases h with rfl | h
    contradiction
    assumption

def sum_select
  [Zero α] [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ]
  [FunLike F α γ] [IsZeroHom F α γ]
  (f: Finsupp ι α S) (g: F):
  f.sum (fun i a => if i = j then g a else 0) (by
    intro i eq
    dsimp; rw [eq, map_zero]
    split <;> rfl) = g (f j) := by
  cases f with | mk f spec =>
  induction spec with | mk spec =>
  obtain ⟨supp, spec⟩ := spec
  show _ = g (f j)
  show Multiset.sum _ = _
  simp
  show (Multiset.map (fun i => if i = j then g (f i) else 0) (supp: LazyFinset ι).toMultiset).sum = _
  replace spec : ∀x: ι, f x ≠ 0 -> x ∈ (supp: LazyFinset _) := spec
  revert spec
  generalize (supp: LazyFinset ι) = supp'
  clear supp
  simp
  intro h
  replace h := h j
  induction supp' with
  | nil =>
    show 0 = _
    suffices f j = 0 by
      rw [this, map_zero]
    apply Classical.byContradiction
    intro h'
    have := h h'
    contradiction
  | cons i supp ne ih =>
    rw [LazyFinset.cons_toMultiset _ _ ne]
    simp
    split
    subst i
    rw [Multiset.sum_eq_zero, add_zero]
    · intro x hx
      rw [Multiset.mem_map] at hx
      obtain ⟨i', hi', eq⟩ := hx
      split at eq
      subst i'
      simp at hi'
      contradiction
      symm; assumption
    rw [zero_add]
    apply ih
    intro hj
    simp [hj] at h
    rcases h with rfl | h
    contradiction
    assumption

private def sum' [Zero α] [∀a: α, Decidable (a = 0)] [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ] (f: Finsupp ι α S) (g: ι -> α -> γ) :=
  (f.support.toMultiset.map (fun i => g i (f i))).sum

private def sum_eq_sum'
   [Zero α] [∀a: α, Decidable (a = 0)] [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ] (f: Finsupp ι α S) (g: ι -> α -> γ) (resp: ∀i: ι, f i = 0 -> g i (f i) = 0):
   f.sum g resp = f.sum' g := by
   rw [sum', sum_eq_support_sum]

def sum_pairwise
   [Zero α] [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ] (f: Finsupp ι α S)
   (g₀: ι -> α -> γ) (resp₀: ∀i: ι, f i = 0 -> g₀ i (f i) = 0)
   (g₁: ι -> α -> γ) (resp₁: ∀i: ι, f i = 0 -> g₁ i (f i) = 0) :
   f.sum g₀ resp₀ + f.sum g₁ resp₁ = f.sum (fun i a => g₀ i a + g₁ i a) (by
    intro i eq
    dsimp; rw [resp₀ _ eq, resp₁ _ eq, add_zero]) := by
  classical
  simp [sum_eq_support_sum]
  apply Multiset.sum_pairwise

def sum_sum_index
  [Zero α] [Add α] [IsAddZeroClass α]
  [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ]
  [AddMonoidOps γ₁] [IsAddCommMagma γ₁] [IsAddMonoid γ₁]
  (f: Finsupp ι α S) (g₀: ι -> α -> Finsupp ι γ S) (g₁: ι -> γ -> γ₁)
  (map_add: ∀i a b, g₁ i (a + b) = g₁ i a + g₁ i b)
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
    classical
    simp [sum_eq_sum' (g := g₁)]
    let sum'_hom : Finsupp ι γ S →+ γ₁ := {
      toFun f := Finsupp.sum' f g₁
      map_zero := ?_
      map_add := ?_
    }
    show sum'_hom _ = _
    rw [map_sum (f₀ := sum'_hom) (f := f) (g := g₀)]
    rfl
    apply Multiset.sum_eq_zero
    intro x h
    rw [Multiset.mem_map] at h
    obtain ⟨i, _, rfl⟩ := h
    apply h₁
    intro x y
    repeat rw [←sum_eq_sum' (g := g₁) (resp := by
      intro i h
      rw [h, h₁])]
    rw [sum_eq_support_max_sum _ _ _ _ (Finsupp.support_add x y)]
    rw [sum_eq_support_max_sum _ _ _ _ (LazyFinset.sub_append_left x.support y.support)]
    rw [sum_eq_support_max_sum _ _ _ _ (LazyFinset.sub_append_right x.support y.support)]
    generalize (x.support ++ y.support).toMultiset = supp
    simp [map_add]
    symm; apply Multiset.sum_pairwise

def sum_eq_pairwise [Zero α] [Zero β]  [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ]
  (f₀: Finsupp ι α S)
  (f₁: Finsupp ι β S)
  (g₀: ι -> α -> γ)
  (g₁: ι -> β -> γ)
  (h₀: ∀i: ι, f₀ i = 0 -> g₀ i (f₀ i) = 0)
  (h₁: ∀i: ι, f₁ i = 0 -> g₁ i (f₁ i) = 0)
  (eq₀: ∀i, g₀ i (f₀ i) = g₁ i (f₁ i))
  : f₀.sum g₀ h₀ = f₁.sum g₁ h₁ := by
  classical
  rw [sum_eq_support_max_sum (s := f₀.support ∪ f₁.support),
    sum_eq_support_max_sum (s := f₀.support ∪ f₁.support)]
  congr; ext i; apply eq₀
  exact LazyFinset.sub_append_right f₀.support f₁.support
  exact LazyFinset.sub_append_left f₀.support f₁.support

end Finsupp
