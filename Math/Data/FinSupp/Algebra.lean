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

def resp_sum
  [Zero α] [Add α] [IsAddZeroClass α]
  [AddMonoidOps γ] [IsAddCommMagma γ] [IsAddMonoid γ]
  [AddMonoidOps γ'] [IsAddCommMagma γ'] [IsAddMonoid γ']
  [FunLike F γ γ'] [IsZeroHom F γ γ'] [IsAddHom F γ γ']
  (f: Finsupp ι α S) (g: ι -> α -> γ) {h} (f₀: F) : f₀ (f.sum g h) = f.sum (fun i a => f₀ (g i a)) (by
    intro i eq
    dsimp
    rw [h _ eq, resp_zero]) := by
    cases f with | mk f spec =>
    induction spec with | mk spec =>
    apply Eq.trans
    apply Multiset.resp_sum
    rw [Multiset.map_map]
    rfl

def sum_single [DecidableEq ι] [AddMonoidOps α] [IsAddMonoid α] [IsAddCommMagma α]
  (f: Finsupp ι α S) : f.sum single (by
    intro i eq
    rw [eq]; ext i ; rw [apply_single]; split <;> rfl) = f := by
    ext i
    let f' : Finsupp ι α S →+ α := {
      toFun x := x i
      resp_zero := rfl
      resp_add := rfl
    }
    show f' _ = _
    rw [resp_sum]
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
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.sum_eq_zero, add_zero, apply_single, if_pos rfl]
    intro i₀ h₀
    rw [Multiset.mem_map] at h₀
    obtain ⟨i₀, h₀, rfl⟩ := h₀
    rw [apply_single, if_neg]
    rintro rfl
    have : (i::ₘas).Nodup := by rw [←eq]; apply f.support.property
    have := this.head
    contradiction

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
    classical
    simp [sum_eq_support_sum]
    generalize f.support.val=fsupp
    induction fsupp with
    | nil =>
      simp
      rw [support_zero]
      rfl
    | cons a as ih =>
      simp [←ih]; clear ih
      rw [←Multiset.sum_append]
      generalize hx:(Multiset.map (fun i => g₀ i (f i)) as).sum = x
      have ⟨s', hs', eq⟩ := Finset.exists_union_eq_of_sub (h := Finsupp.support_add (g₀ a (f a)) x)
      have : ∀x ∈ s', f x = 0 := sorry
      sorry

end Finsupp
