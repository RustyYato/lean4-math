import Math.Data.Real.MetricSpace

namespace Real

instance isInterval.range (I: Set ℝ) [IsInterval I] (f: I -> ℝ) [Topology.IsContinuous f] :
  IsInterval (Set.range f) where
  isInterval := by
    intro _ _ hy₀ hy₁ l y₀_le_l l_le_y₁
    obtain ⟨⟨y₀, hy₀⟩ , rfl⟩ := hy₀
    obtain ⟨⟨y₁, hy₁⟩ , rfl⟩ := hy₁
    apply Set.mem_range.mpr
    let S := Set.mk fun x => ∃h: x ∈ I, f ⟨x, h⟩ ≤ l
    let T := Set.mk fun x => ∃h: x ∈ I, f ⟨x, h⟩ ≥ l
    have I_eq_S_union_T : I = S ∪ T := by
      ext i
      apply Iff.intro
      intro hi
      rcases lt_or_le (f ⟨i, hi⟩) l with lt | le
      left; exists hi; apply le_of_lt; assumption
      right; exists hi
      intro h
      rcases h with ⟨h, g⟩ | ⟨h, g⟩
      assumption
      assumption
    have y₀_in_S : y₀ ∈ S := ⟨hy₀, y₀_le_l⟩
    have y₁_in_Y : y₁ ∈ T := ⟨hy₁, l_le_y₁⟩
    -- have := sInf (T.image (dist · l))
    sorry

def intermediate_value_theorem (I: Set ℝ) [IsInterval I] (f: I -> ℝ) [Topology.IsContinuous f] :
  ∀{a b: ℝ} (ha: a ∈ I) (hb: b ∈ I),
  ∀k, f ⟨a, ha⟩ ≤ k -> k ≤ f ⟨b, hb⟩ ->
  k ∈ Set.range f := by
  intro a b ha hb
  apply Set.mem_interval (Set.range f)
  apply Set.mem_range'
  apply Set.mem_range'

end Real
