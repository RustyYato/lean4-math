import Math.Algebra.Module.SetLike.Lattice
import Math.Algebra.Field.Defs
import Math.Data.List.Algebra
import Math.Algebra.Group.Action.Basic

namespace Submodule

section Defs

variable (R: Type*) [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M] [SMul R M] [IsModule R M]

-- the span of a set is the set of all vectors that are made from linear combinations it
def span : Set M -> Submodule R M := generate

def mem_span_of (U: Set M) : ∀x ∈ U, x ∈ span R U := by
  intro x h
  apply Generate.of
  assumption

def linindep (U: Set M) : Prop :=
  -- a (possibly infinite) set is linearly independent if
  -- every finite subset of it is linearly independent
  -- i.e. if every vector in the subset is not contained in the span
  -- of all other vectors in the subset
  ∀s: List M, Set.ofList s ⊆ U ->
    ∀m ∈ s, m ∉ span R (Set.ofList s \ {m})

structure IsBasis (U: Set M) : Prop where
  indep: linindep R U
  complete: ∀m, m ∈ span R U

end Defs

section Span

variable [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M] [SMul R M] [IsModule R M]

def span_sub {U V: Set M} (u: U ⊆ V) : span R U ⊆ span R V := by
  intro x v
  apply of_mem_generate _ _ _ _ v
  intro m hm
  apply Generate.of
  apply u
  assumption

def linear_combination (xs: List (R × M)) : M :=
  List.sum (xs.map fun (r, m) => r • m)

def smul_linear_combination (r: R) (xs: List (R × M)) :
  r • linear_combination xs = linear_combination  (xs.map fun (r₀, x) => (r * r₀, x)) := by
  induction xs with
  | nil => apply smul_zero
  | cons x xs ih =>
    obtain ⟨r₀, x⟩ := x
    dsimp
    unfold linear_combination
    simp [List.map_cons, List.sum_cons, smul_add, mul_smul]
    rw [←linear_combination, ih, linear_combination, List.map_map]

def linear_combination_extract'
   (xs: List (R × M)) (i: Nat) (hi: i < xs.length):
  linear_combination xs = xs[i].fst • xs[i].snd + linear_combination (xs.eraseIdx i) := by
  induction i generalizing xs with
  | zero =>
    cases xs with
    | nil => contradiction
    | cons x xs => rfl
  | succ i ih =>
    cases xs with
    | nil => contradiction
    | cons x xs =>
      dsimp
      unfold linear_combination
      simp [List.map_cons]
      rw [add_left_comm, ←linear_combination, ih]
      rfl

def linear_combination_cons (a: R × M) (as: List (R × M)) :
  linear_combination (a::as) = a.fst • a.snd + linear_combination as := rfl

def linear_combination_extract
   (x: R × M) (as bs: List (R × M)):
  linear_combination (as ++ x::bs) = x.fst • x.snd + linear_combination (as ++ bs) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp [linear_combination_cons, ih]
    rw [add_left_comm]

def mem_span (U: Set M) : ∀x, x ∈ span R U ↔
  ∃l: List (R × M),
    (Set.mk fun m: M => ∃r, (r, m) ∈ l) ⊆ U ∧
    x = linear_combination l := by
  intro m
  apply Iff.intro
  · intro h
    induction h with
    | of v hv =>
      clear m
      exists [(1, v)]
      simp [linear_combination, one_smul]
      rintro _ rfl
      assumption
    | zero =>
      exists []
      simp [linear_combination]
      apply Set.empty_sub
    | add _ _ ha hb =>
      obtain ⟨as, as_sub, rfl⟩ := ha
      obtain ⟨bs, bs_sub, rfl⟩ := hb
      exists as ++ bs
      simp
      apply And.intro
      · intro x hx
        simp at hx
        obtain ⟨r, h|h⟩ := hx
        apply as_sub
        exists r
        apply bs_sub
        exists r
      symm; unfold linear_combination
      rw [List.map_append]
      apply List.sum_append
    | smul r _ ih =>
      obtain ⟨as, as_sub, rfl⟩ := ih
      exists as.map (fun (r₀, x) => (r * r₀, x))
      simp
      rw [smul_linear_combination]
      apply And.intro _ rfl
      intro x hx
      simp at hx
      apply as_sub
      obtain ⟨r₀, r₁, mem, rfl⟩ := hx
      simp
      exists r₁
  · rintro ⟨l, mem, rfl⟩
    induction l with
    | nil =>
      apply mem_zero
    | cons l ls ih =>
      apply mem_add
      apply mem_smul
      apply Generate.of
      apply mem
      exists l.fst
      apply List.Mem.head
      apply ih
      apply Set.sub_trans _ mem
      intro x ⟨r, hx⟩
      exists r
      simp [hx]

end Span

section Field

variable [FieldOps R] [IsField R] [AddGroupOps M] [IsAddGroup M] [IsAddCommMagma M] [SMul R M] [IsModule R M]

def linear_indep_iff (U: Set M) :
  linindep R U ↔ ∀l: List (R × M), Set.mk (fun m: M => ∃r: R, (r, m) ∈ l) ⊆ U ->
  linear_combination l = 0 -> ∀x ∈ l, x.fst = 0 := by
  apply Iff.intro
  · intro indep l
    induction l with
    | nil => simp
    | cons a l ih =>
      obtain ⟨r, m⟩ := a
      intro h eq (r₀, m₀) mem
      rw [linear_combination_cons] at eq
      dsimp at eq
      have m₀_notin_span := indep (l.map (·.snd)) ?_ m₀ ?_
      dsimp
      cases mem
      rw [add_eq_iff_eq_sub, zero_sub] at eq
      apply Classical.byContradiction
      intro hr
      replace eq : r⁻¹? • (r • m) = r⁻¹? • (-linear_combination l) := by rw [eq]
      rw [smul_neg, ←neg_smul, ←mul_smul, inv?_mul_cancel, one_smul,
        smul_linear_combination] at eq
      apply m₀_notin_span; clear m₀_notin_span
      rw [mem_span]
      dsimp at eq
      refine ⟨l.map (fun x => (-r⁻¹? * x.fst, x.snd)), ?_, eq⟩
      · intro m₀ ⟨r₀, mem⟩
        rw [List.mem_map] at mem
        obtain ⟨⟨r₁, m₁⟩, mem₁, eq⟩ := mem
        cases eq
        dsimp
        apply And.intro
        rw [Set.ofList, Set.mk_mem, List.mem_map]
        exists (r₁, m₁)
        rintro rfl
        sorry
      · sorry
      · sorry
      · sorry
  · sorry

def linindep_insert (m: M) (U: Set M) (h: m ∉ span R U) :
  linindep R U -> linindep R (insert m U) := by
  classical
  intro g
  intro ms sub v hv
  by_cases hm:m ∈ ms
  by_cases mne:m = v
  · subst v
    intro hv'
    have : Set.ofList ms \ {m} ⊆ U := by
      intro v hv
      have := sub  v hv.left
      simp at this
      cases this
      subst m
      have := hv.right
      contradiction
      assumption
    have := span_sub (V := U) ?_ _ hv'
    contradiction
    assumption
  · rw [mem_span]
    rintro ⟨l, sub_l, rfl⟩
    -- have := g (ms.erase m) ?_ v ?_
    have := g (l.map (·.2)) sorry m



    repeat sorry
  -- · by_cases hv:v = 0
  --   · subst v
  --     clear hv

  --     sorry
  --   intro vspan; apply h; clear h
  --   obtain ⟨l, l_sub, rfl⟩ := (mem_span _ _).mp vspan
  --   induction l with
  --   | nil =>

  --     sorry
  --   | cons l ls ih => sorry
  · apply g
    intro v hv
    have := sub v hv
    simp at this
    cases this
    subst v
    contradiction
    assumption
    assumption

end Field

end Submodule
