import Math.Algebra.Field.Defs
import Math.Algebra.Module.Submodule
import Math.Order.Zorn

variable (R M: Type*) [FieldOps R] [IsField R] [AddGroupOps M] [IsAddGroup M] [IsAddCommMagma M] [SMul R M] [IsModule R M]

def existsBasis : ∃s: Set M, Submodule.IsBasis R s := by
  classical
  have ⟨S, linear_indep, spec⟩ := Zorn.subset (Set.mk (Submodule.IsLinindep R (M := M))) ?_
  · refine ⟨S, linear_indep, ?_⟩
    apply Classical.byContradiction
    intro h
    simp at h
    obtain ⟨m, m_not_in_span⟩ := h
    suffices Submodule.IsLinindep R (insert m S) by
      have := spec (insert m S) this ?_
      have : m ∈ S := by
        rw [←this]
        simp
      have := Submodule.mem_span_of R _ _ this
      contradiction
      apply Set.sub_insert
    · apply Submodule.insertLinindep
      assumption
      assumption
  · intro S mem_S_linear_indep Schain
    refine ⟨⋃S, ?_, fun _ => Set.sub_sUnion _ _⟩
    rcases S.empty_or_nonempty with rfl | ⟨s, hS⟩
    · intro C suppC eq_zero
      rw [Set.sUnion_empty] at suppC
      ext m
      apply Classical.byContradiction
      intro h
      replace h : m ∈ Set.support C := h
      rw [Set.of_sub_empty _ suppC] at h
      contradiction
    · intro C suppC eq_zero
      suffices ∃s ∈ S, Set.support C ⊆ s ∧ Submodule.IsLinindep R s by
        obtain ⟨s, _, supp_s, linindep⟩ := this
        exact linindep C supp_s eq_zero
      clear eq_zero
      induction C with
      | zero =>
        exists s
        apply And.intro
        assumption
        apply And.intro
        intro x h; contradiction
        apply mem_S_linear_indep
        assumption
      | add a b ha hb h g =>
        rw [h] at suppC
        clear g
        replace ⟨sa, sa_mem, supp_sa, ha⟩ := ha (Set.sub_trans (Set.sub_union_left _ _) suppC)
        replace ⟨sb, sb_mem, supp_sb, hb⟩ := hb (Set.sub_trans (Set.sub_union_right _ _) suppC)
        exists sa ∪ sb
        have : sa ∪ sb = if sa ⊆ sb then sb else sa := ?_
        apply And.intro
        rw [this]
        split <;> assumption
        rw [h]
        apply And.intro
        intro m hm
        rcases hm with hm | hm
        left; apply supp_sa; assumption
        right; apply supp_sb; assumption
        rw [show sa ∪ sb = if sa ⊆ sb then sb else sa from ?_]
        split <;> assumption
        assumption
        have : sa ⊆ sb ∨ _ ∨ sb ⊆ sa := Schain.tri ⟨sa, sa_mem⟩ ⟨sb, sb_mem⟩
        rcases this with h | h | h
        rw [Set.union_of_sub_left h]
        rw [if_pos h]
        cases h
        rw [Set.union_self]
        split <;> rfl
        rw [Set.union_of_sub_right h]
        split
        apply Set.sub_antisymm
        assumption
        assumption
        rfl
      | single r m hr =>
        rcases LinearCombination.support_single r m with h | h
        rw [h] at *
        exists s
        apply And.intro
        assumption
        apply And.intro
        apply Set.empty_sub
        apply mem_S_linear_indep
        assumption
        rw [h] at suppC; rw [h]
        clear h
        have ⟨s', s'_mem, h⟩ := suppC m (by simp)
        exists s'
        apply And.intro
        assumption
        apply And.intro
        rintro _ rfl
        assumption
        apply mem_S_linear_indep
        assumption

noncomputable def basis : Set M := Classical.choose (existsBasis R M)
def basis_is_basis : Submodule.IsBasis R (basis R M) := Classical.choose_spec (existsBasis R M)
def basis_is_linear_indep : Submodule.IsLinindep R (basis R M) := (basis_is_basis R M).indep
def basis_is_spanning_set : ∀m, m ∈ Submodule.span R (basis R M) := (basis_is_basis R M).complete
def basis_span_eq_univ : Submodule.span R (basis R M) = ⊤ := by
  ext
  apply Iff.intro <;> intro
  trivial
  apply basis_is_spanning_set
