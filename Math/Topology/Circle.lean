-- the topology S₁

import Math.Data.Real.MetricSpace
import Math.Topology.Filter.Defs

open Topology

@[local instance]
def S₁.setoid : Setoid ℝ where
  r a b := ∃i: ℤ, a - b = i
  iseqv := {
    refl x := ⟨0, by rw [sub_self, intCast_zero]⟩
    symm := by
      intro x y ⟨i, eq⟩
      exists -i
      rw [←neg_sub, eq, intCast_neg]
    trans := by
      intro x y z ⟨i, hi⟩ ⟨j, hj⟩
      exists i + j
      rw [←add_zero x, ←neg_add_cancel y, ←add_assoc, add_sub_assoc,
        ←sub_eq_add_neg, hi, hj, intCast_add]
  }

def Real.Icc_compact (a b: ℝ) (h: a ≤ b) : Topology.IsCompactOn (Set.Icc a b) := by
  intro F _ h
  have := h (Set.Icc a b) (FilterBase.mem_principal_self _)
  exists a
  apply And.intro
  apply And.intro
  apply le_refl (α := ℝ)
  assumption
  refine ⟨?_⟩
  suffices ∅ ∉ (𝓝 a) ⊓ F by
    intro h; apply this
    rw [h]; trivial
  intro g
  obtain ⟨U, U_sub, U_finite, sInf_U_le_empty⟩ := (FilterBase.mem_generate_iff (α := Set ℝ) (ne := (by exists ⊤; simp))).mp g
  replace U_sub : ∀u ∈ U, ∃ f₀ f₁, f₀ ∈ 𝓝 a ∧ f₁ ∈ F ∧ u = f₀ ⊓ f₁ := by
    intro s hS
    have := U_sub s hS
    cases this
    subst s
    exists ⊤
    exists ⊤
    refine ⟨?_, ?_, ?_⟩
    apply Filter.univ_mem
    apply Filter.univ_mem
    rw [min_self]
    rename_i h'
    exact h'
  have sInter_empty : ∀x, x ∉ ⋂U := by
    intro x g
    have := sInf_U_le_empty x g
    contradiction
  clear sInf_U_le_empty
  let get_f₀' (u: Set ℝ) (hu: u ∈ U) : Set ℝ :=
    Classical.choose (U_sub u (by
      assumption))
  let get_f₁' (u: Set ℝ) (hu: u ∈ U) : Set ℝ :=
    Classical.choose <|
    Classical.choose_spec (U_sub u (by
      assumption))
  have spec₀' (u: Set ℝ) (hu: u ∈ U) : (get_f₀' u hu) ∈ 𝓝 a :=
    (Classical.choose_spec <|
    Classical.choose_spec (U_sub u (by
      assumption))).left
  have spec₁' (u: Set ℝ) (hu: u ∈ U) : (get_f₁' u hu) ∈ F :=
    (Classical.choose_spec <|
    Classical.choose_spec (U_sub u (by
      assumption))).right.left
  have spec₂' (u: Set ℝ) (hu: u ∈ U) : u = (get_f₀' u hu) ∩ (get_f₁' u hu) :=
    (Classical.choose_spec <|
    Classical.choose_spec (U_sub u (by
      assumption))).right.right
  let f₀ : Set ℝ := ⨅i: U, get_f₀' i i.property
  let f₁ : Set ℝ := ⨅i: U, get_f₁' i i.property
  have f₀_in_nhbd : f₀ ∈ 𝓝 a := by
    apply (FilterBase.closed_finite_sInf _ _).mpr
    intro s hs
    simp [Set.mem_range] at hs
    obtain ⟨s, s_in_U, rfl⟩ := hs
    apply spec₀'
    assumption
  have f₁_in_F : f₁ ∈ F := by
    apply (FilterBase.closed_finite_sInf _ _).mpr
    intro s hs
    simp [Set.mem_range] at hs
    obtain ⟨s, s_in_U, rfl⟩ := hs
    apply spec₁'
    assumption
  have spec : ⋂ U = f₀ ∩ f₁ := by
    ext x
    apply Iff.intro
    intro h
    rw [Set.mem_sInter] at h
    rw [Set.mem_inter]
    apply And.intro
    apply Set.mem_sInter.mpr
    rintro _ ⟨⟨s, hs⟩, rfl⟩
    have := h s hs
    simp
    rw [spec₂' s hs] at this
    rw [Set.mem_inter] at this
    exact this.left
    apply Set.mem_sInter.mpr
    rintro _ ⟨⟨s, hs⟩, rfl⟩
    have := h s hs
    simp
    rw [spec₂' s hs] at this
    rw [Set.mem_inter] at this
    exact this.right
    intro hx s hs
    rw [spec₂' s hs]
    apply And.intro
    exact hx.left _ ⟨⟨s, hs⟩, rfl⟩
    exact hx.right _ ⟨⟨s, hs⟩, rfl⟩
  rw [spec] at sInter_empty
  rw [mem_nhds] at f₀_in_nhbd
  obtain ⟨s, hs, sopen, a_in_s⟩ := f₀_in_nhbd
  have ⟨δ, δpos, ball_sub⟩ := sopen _ a_in_s
  rw [←not_exists] at sInter_empty
  apply sInter_empty; clear sInter_empty









  sorry

def S₁ := Quotient S₁.setoid

namespace S₁

def mk : ℝ -> S₁ := Quotient.mk _

instance : Nonempty S₁ := ⟨mk 0⟩

instance : Topology S₁ := inferInstanceAs (Topology (Quotient S₁.setoid))

instance : Topology.IsCompactSpace S₁ where
  univ_compact := by
    intro F _ le
    refine ⟨mk 0, by trivial, ?_⟩
    clear le
    refine ⟨?_⟩
    suffices ∅ ∉ (𝓝 (mk 0)) ⊓ F by
      intro h; apply this
      rw [h]; trivial
    intro h
    have ⟨U, U_sub, U_finite, sInfU_le⟩ := (FilterBase.mem_generate_iff (α := Set S₁) (ne := (by exists ⊤; simp))).mp h
    have : ∀x, x ∉ ⋂U := by
      intro x g
      have := sInfU_le x g
      continuity
    clear sInfU_le
    replace U_sub :
      ∀u ∈ U, ∃ f₀ f₁, f₀ ∈ 𝓝 (mk 0) ∧ f₁ ∈ F ∧ u = f₀ ⊓ f₁ := by
        intro s hS
        have := U_sub s hS
        cases this
        subst s
        exists ⊤
        exists ⊤
        refine ⟨?_, ?_, ?_⟩
        apply Filter.univ_mem
        apply Filter.univ_mem
        rw [min_self]
        rename_i h
        exact h
    induction U using Set.IsFinite.induction with
    | nil =>
      have := this (mk 0)
      rw [Set.mem_sInter] at this
      simp at this
      obtain ⟨_, _, _⟩ := this
      contradiction
    | cons s U s_notin_U Ufin ih =>
      replace ih := ih Ufin
      obtain ⟨f₀, f₁, f₀_in, f₁_in, seq⟩ := U_sub s (by simp)
      rw [Topology.mem_nhds] at f₀_in
      obtain ⟨t, t_sub_f₀, topen, zero_in_t⟩ := f₀_in
      replace topen : IsOpen (t.preimage mk) := topen

      sorry
    -- have := le x
    sorry

end S₁
