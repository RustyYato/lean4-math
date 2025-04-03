import Math.Topology.Basic
import Math.Data.Real.MetricSpace
import Math.Data.NNReal.Basic

instance : Topology ℝ≥0 := inferInstanceAs (Topology (Subtype _))

instance : IsTopologicalSemiring ℝ≥0 where
  continuous_add := by
    apply Topology.IsContinuous.subtype_mk
    continuity
  continuous_mul := by
    apply Topology.IsContinuous.subtype_mk
    continuity

instance : Topology.IsConnected ℝ≥0 where
  univ_preconnected := by
    suffices ∀U V: Set ℝ≥0, Topology.IsOpen U -> Topology.IsOpen V ->
      ⊤ ⊆ U ∪ V -> U.Nonempty -> V.Nonempty -> 0 ∈ U -> 0 ∉ V -> (U ∩ V).Nonempty by
      intro U V hU hV total
      simp; intro neU neV
      classical
      rcases total 0 (by trivial) with hu | hv
      refine if hv:0 ∈ V then ?_ else ?_
      exists 0
      apply this
      any_goals assumption
      rw [Set.inter_comm]
      refine if hv:0 ∈ U then ?_ else ?_
      exists 0
      apply this; any_goals assumption
      rwa [Set.union_comm]
    intro U V hU hV total neU neV U₀ V₀
    obtain ⟨U, hU, rfl⟩ := hU
    obtain ⟨V, hV, rfl⟩ := hV
    have := Topology.IsPreconnected.univ_preconnected (U ∪ Set.Iio 0) (V ∩ Set.Ioi 0) ?_ ?_ ?_ ?_ ?_
    · simp at this
      obtain ⟨x, x_in_u, x_in_v, x_gt_zero⟩ := this
      rcases x_in_u with x_in_u | x_lt_zero
      exists ⟨x, le_of_lt (α := ℝ) x_gt_zero⟩
      have := lt_asymm (α := ℝ) x_gt_zero x_lt_zero
      contradiction
    · apply Topology.IsOpen.union
      assumption
      exact Real.iio_open 0
    · apply Topology.IsOpen.inter
      assumption
      exact Real.ioi_open 0
    · intro x hx
      rcases lt_trichotomy x 0 with x_lt_zero | rfl | zero_lt_x
      left; right; assumption
      left; left; assumption
      rcases total ⟨x, le_of_lt zero_lt_x⟩ (by trivial) with h | h
      left; left; assumption
      right; apply And.intro
      assumption
      assumption
    · simp
      obtain ⟨x, hx⟩ := neU
      exists x.val
      left; assumption
    · simp
      obtain ⟨x, hx⟩ := neV
      exists x.val
      apply And.intro
      assumption
      show 0 < x
      apply lt_of_not_le
      intro h
      cases le_antisymm h (bot_le _)
      contradiction

instance : Topology.IsOrderClosed ℝ≥0 :=
  inferInstanceAs (Topology.IsOrderClosed (Subtype _))
