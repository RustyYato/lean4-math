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
  · intro S Ssub Schain
    refine ⟨⋃S, ?_, ?_⟩
    · sorry
    · sorry
