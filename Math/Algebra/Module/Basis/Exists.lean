import Math.Algebra.Field.Defs
import Math.Algebra.Module.Submodule
import Math.Order.Zorn

variable (R M: Type*) [FieldOps R] [IsField R] [AddGroupOps M] [IsAddGroup M] [IsAddCommMagma M] [SMul R M] [IsModule R M]
  [DecidableEq M]

def existsBasis : Nonempty (Submodule.Basis R M) := by
  classical
  have ⟨S, linear_indep, spec⟩ := Zorn.subset (Set.mk (Submodule.IsLinindep R (M := M))) ?_
  · refine ⟨S, linear_indep, ?_⟩
    apply Classical.byContradiction
    intro h
    simp at h
    obtain ⟨v, hv⟩ := h
    have := spec (insert v S) (Submodule.insertLinindep _ linear_indep v hv) Set.sub_insert
    apply hv
    rw [←this]
    apply Submodule.mem_span_of
    simp
  · intro S memS Schain
    refine ⟨⋃S, ?_, fun _ => Set.sub_sUnion _ _⟩
    show Submodule.IsLinindep _ _
    rw [Submodule.is_linindep_iff_kernel_zero]
    rcases S.empty_or_nonempty with rfl | ⟨s, hs⟩
    · rw [Set.sUnion_empty]
      intro f h
      apply Subsingleton.allEq
    · intro C hC
      suffices ∃s ∈ S, Set.support C ⊆ s.preimage Subtype.val by
        obtain ⟨s, hs, supp⟩ := this
        have s_linindep : Submodule.IsLinindep R s := memS s hs
        rw [Submodule.is_linindep_iff_kernel_zero] at s_linindep
        ext x
        apply Classical.byContradiction
        intro g
        have : x ∈ Set.support C := by assumption
        replace : x.val ∈ s := supp _ this
        replace g : C x ≠ 0 := g
        have ⟨S', hS', gS'⟩ := LinearCombo.exists_superset_of_support C supp
        rw [hC] at hS'
        have := gS' x.val x.property (by assumption)
        rw [this, s_linindep _ hS'.symm] at g
        contradiction
      clear hC
      induction C with
      | zero =>
        exists s
        apply And.intro
        assumption
        erw [Set.support_const_zero]
        apply Set.empty_sub
      | smul r a hr ih  =>
        obtain ⟨s, hs, gs⟩ := ih
        exists s
        apply And.intro
        assumption
        apply Set.sub_trans _ gs
        intro x hx h; apply hx
        show r * a x = 0
        rw [h, mul_zero]
      | add a b iha ihb hadd hinter =>
        have : Set.support (a + b) = Set.support a ∪ Set.support b := by
          ext x
          simp [Set.mem_support, Set.mem_union]
          apply Iff.intro
          intro h
          apply Classical.or_iff_not_imp_left.mpr
          simp; intro g; rwa [g, zero_add] at h
          intro h g
          cases hadd _ g
          rcases h with h | h <;> contradiction
        obtain ⟨sa , hsa, gsa⟩ := iha
        obtain ⟨sb , hsb, gsb⟩ := ihb
        rw [this]
        rcases Relation.total (Set.Induced (· ⊆ (·: Set M)) S) ⟨sa, hsa⟩ ⟨sb, hsb⟩ with h | h
        replace h : sa ⊆ sb := h
        exists sb
        apply And.intro
        assumption
        rw [←Set.union_sub]
        apply And.intro
        apply Set.sub_trans
        assumption
        intro x; apply h
        assumption
        replace h : sb ⊆ sa := h
        exists sa
        apply And.intro
        assumption
        rw [←Set.union_sub]
        apply And.intro
        assumption
        apply Set.sub_trans
        assumption
        intro x; apply h
      | ι m hm =>
        obtain ⟨t, ht, hm⟩ := hm
        exists t
        apply And.intro
        assumption
        intro x hx
        rw [Set.mem_support, LinearCombo.apply_ι] at hx
        simp at hx
        cases hx.left
        assumption

noncomputable def basis : Submodule.Basis R M := Classical.choice (existsBasis R M)
