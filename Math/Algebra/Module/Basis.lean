import Math.Algebra.Field.Defs
import Math.Algebra.Module.Submodule
import Math.Order.Zorn

variable (R M: Type*) [FieldOps R] [IsField R] [AddGroupOps M] [IsAddGroup M] [IsAddCommMagma M] [SMul R M] [IsModule R M]

def existsBasis : ∃s: Set M, Submodule.IsBasis R s := by
  classical
  have ⟨S, linear_indep, spec⟩  := Zorn.subset (Set.mk (Submodule.IsLinindep R (M := M))) ?_
  · refine ⟨S, linear_indep, ?_⟩
    apply Classical.byContradiction
    intro h
    simp at h
    obtain ⟨m, m_not_in_span⟩ := h
    have := spec (insert m S) ?_ ?_
    · have : m ∈ S := by
        rw [←this]
        simp
      have := Submodule.mem_span_of R _ _ this
      contradiction
    · intro C sub eq
      rw [←add_zero C, ←sub_self (LinearCombination.single (C m) m),
        sub_eq_add_neg, add_left_comm, ←sub_eq_add_neg,
        add_comm, resp_add,
        LinearCombination.single_valHom] at eq
      by_cases hc:C m = 0
      simp [hc, resp_sub] at eq
      apply linear_indep C _ eq
      intro x hx
      cases sub x hx
      subst x
      contradiction
      assumption
      replace eq := (neg_eq_of_add_left eq).symm
      replace eq : (C m)⁻¹? • (C m • m) = (C m)⁻¹? • (-LinearCombination.valHom (C - LinearCombination.single (C m) m)) := by
        rw [eq]
      rw [←mul_smul, inv?_mul_cancel, one_smul, ←resp_neg, ←resp_smul] at eq
      exfalso; apply m_not_in_span
      refine ⟨_, ?_, eq⟩
      have : Set.support (((C m)⁻¹? • -(C - LinearCombination.single (C m) m)): LinearCombination R M) ⊆ Set.support C := by
        intro v h
        simp [Set.mem_support, neg_sub, mul_sub] at h
        intro g
        rw [g, mul_zero, sub_zero, LinearCombination.apply_single] at h
        split at h
        subst v
        contradiction
        simp at h
      intro v h
      have h' := this v h
      have := sub _ h'
      simp at this
      cases this
      · subst v
        rw [Set.mem_support] at h h'
        exfalso
        apply m_not_in_span
        simp [neg_sub, mul_sub, inv?_mul_cancel, LinearCombination.apply_single] at h
      · assumption
    · apply Set.sub_insert
  · intro S mem_S_linear_indep Schain
    refine ⟨⋃S, ?_, ?_⟩
    · by_cases hS:S.Nonempty
      · obtain ⟨s, hS⟩ := hS
        intro C suppC eq_zero
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
        | single r m =>
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
      · intro C suppC eq_zero
        cases Set.not_nonempty _ hS
        suffices Set.support C = ∅ by
          ext m
          apply Classical.byContradiction
          intro h
          replace h : m ∈ Set.support C := h
          rw [this] at h
          contradiction
        apply Set.ext_empty
        intro m h
        have := suppC m h
        rw [Set.sUnion_empty] at this
        contradiction
    · intro; apply Set.sub_sUnion

noncomputable def basis : Set M := Classical.choose (existsBasis R M)
def basis_is_basis : Submodule.IsBasis R (basis R M) := Classical.choose_spec (existsBasis R M)
def basis_is_linear_indep : Submodule.IsLinindep R (basis R M) := (basis_is_basis R M).indep
def basis_is_spanning_set : ∀m, m ∈ Submodule.span R (basis R M) := (basis_is_basis R M).complete
def basis_span_eq_univ : Submodule.span R (basis R M) = ⊤ := by
  ext
  apply Iff.intro <;> intro
  trivial
  apply basis_is_spanning_set
