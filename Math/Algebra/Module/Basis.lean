import Math.Algebra.Field.Defs
import Math.Algebra.Module.Submodule
import Math.Order.Zorn

variable (R M: Type*) [FieldOps R] [IsField R] [AddGroupOps M] [IsAddGroup M] [IsAddCommMagma M] [SMul R M] [IsModule R M]

structure PreBasis where
  set: Set M
  linear_indep: Submodule.IsLinindep R set

namespace PreBasis

instance : LE (PreBasis R M) where
  le a b := a.set ≤ b.set
instance : LT (PreBasis R M) where
  lt a b := a.set < b.set

def orderEmbed : PreBasis R M ↪o Set M where
  toFun := set
  inj' := by intro a b eq; cases a; congr
  resp_rel := Iff.rfl

instance : IsLawfulLT (PreBasis R M) where
  lt_iff_le_and_not_le := lt_iff_le_and_not_le (α := Set M)

instance : IsPartialOrder (PreBasis R M) :=
  (orderEmbed R M).inducedIsPartialOrder'

def existsBasis : ∃s: Set M, Submodule.IsBasis R s := by
  have ⟨s, spec⟩ := Zorn.partialorder (α := PreBasis R M) ?_
  · refine ⟨s.set, s.linear_indep, ?_⟩
    apply Classical.byContradiction
    intro h
    simp at h
    obtain ⟨m, m_not_in_span⟩ := h
    have := spec {
      set := insert m s.set
      linear_indep := ?_
    } ?_
    have : m ∈ s.set := by
      rw [←this]
      simp
    have := Submodule.mem_span_of R _ _ this
    contradiction
    sorry
    sorry
  · sorry

end PreBasis
