import Math.Algebra.Module.SetLike.Lattice
import Math.Algebra.Field.Defs
import Math.Algebra.Group.Action.Basic
import Math.Algebra.Module.LinearCombo

namespace Submodule

section Defs

open Classical

variable {M: Type*} (R: Type*) [SemiringOps R] [IsSemiring R] [AddMonoidOps M] [IsAddMonoid M] [IsAddCommMagma M] [SMul R M] [IsModule R M]

-- the span of a set is the set of all vectors that are made from
-- linear combinations of members of the set
def span (U: Set M) : Submodule R M where
  carrier := Set.mk fun v => ∃f: LinearCombination R M, Set.support f ⊆ U ∧ v = f
  mem_zero' := ⟨0, by
    intro v h
    rw [Set.mem_support] at h
    contradiction , rfl⟩
  mem_add' := by
    rintro a b ⟨fa, ha, rfl⟩ ⟨fb, hb, rfl⟩
    exists fa + fb
    apply And.intro
    · intro v h
      rw [Set.mem_support] at h
      replace h : fa v + fb v ≠ 0 := h
      by_cases g:fa v = 0
      rw [g] at h
      simp at h
      apply hb v
      rw [Set.mem_support]
      assumption
      apply ha v
      rw [Set.mem_support]
      assumption
    · rw [resp_add]
  mem_smul' := by
    rintro r _ ⟨f, hf, rfl⟩
    exists r • f
    apply And.intro
    · intro v h
      rw [Set.mem_support] at h
      replace h : r • f v ≠ 0 := h
      by_cases g:f v = 0
      rw [g] at h
      simp at h
      apply hf
      rw [Set.mem_support]
      assumption
    · rw [resp_smul]

def mem_span_of (U: Set M) : ∀x ∈ U, x ∈ span R U := by
  intro x h
  exists LinearCombination.single 1 x
  apply And.intro
  intro y hy
  cases (LinearCombination.mem_support_single hy).right
  assumption
  simp

def span_eq_generate (U: Set M) : span R U = generate U := by
  ext x
  apply Iff.intro
  · rintro ⟨f, h, rfl⟩
    induction f with
    | zero =>
      apply mem_zero
    | add f₀ f₁ h₀ h₁ g =>
      rw [g] at h
      rw [resp_add]
      apply mem_add
      · apply h₀
        intro x hx
        apply h
        left; assumption
      · apply h₁
        intro x hx
        apply h
        right; assumption
    | single r m =>
      show LinearCombination.val (LinearCombination.single _ _) ∈ _
      rw [LinearCombination.single_val]
      apply mem_smul
      apply Generate.of
      apply h m
      rw [Set.mem_support, LinearCombination.apply_single, if_pos rfl]
      assumption
  · intro h
    apply of_mem_generate _ _ _ _ h
    intro v hv
    apply mem_span_of
    assumption

-- a set is linearly independent if every non-trivial linear combination is non-zero
def IsLinindep (U: Set M) := ∀f: LinearCombination R M,
  Set.support f ⊆ U -> (f: M) = 0 -> f = 0

structure IsBasis (U: Set M) : Prop where
  indep: IsLinindep R U
  complete: ∀m, m ∈ span R U

end Defs

section

variable {R M: Type*} [FieldOps R] [IsField R] [AddGroupOps M] [IsAddGroup M] [IsAddCommMagma M] [SMul R M] [IsModule R M]

def insertLinindep (S: Set M) (hS: Submodule.IsLinindep R S) (m: M) (hm: m ∉ Submodule.span R S) : Submodule.IsLinindep R (insert m S) := by
  classical
  intro C sub eq
  rw [←add_zero C, ←sub_self (LinearCombination.single (C m) m),
    sub_eq_add_neg, add_left_comm, ←sub_eq_add_neg,
    add_comm, resp_add,
    LinearCombination.single_valHom] at eq
  by_cases hc:C m = 0
  simp [hc, resp_sub] at eq
  apply hS C _ eq
  intro x hx
  cases sub x hx
  subst x
  contradiction
  assumption
  replace eq := (neg_eq_of_add_left eq).symm
  replace eq : (C m)⁻¹? • (C m • m) = (C m)⁻¹? • (-LinearCombination.valHom (C - LinearCombination.single (C m) m)) := by
    rw [eq]
  rw [←mul_smul, inv?_mul_cancel, one_smul, ←resp_neg, ←resp_smul] at eq
  exfalso; apply hm
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
    apply hm
    simp [neg_sub, mul_sub, inv?_mul_cancel, LinearCombination.apply_single] at h
  · assumption

end

end Submodule
