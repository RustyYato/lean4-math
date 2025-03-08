import Math.Data.Real.MetricSpace

namespace Real

def isInterval (I: Set ℝ) : Prop :=
  ∀⦃x y⦄, x ∈ I -> y ∈ I -> ∀z, x ≤ z -> z ≤ y -> z ∈ I

def isInterval.range (I: Set ℝ) (hI: isInterval I) (f: I -> ℝ) [Topology.IsContinuous f] :
  isInterval (Set.range f) := by
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

def intermediate_value_theorem (I: Set ℝ) (hI: isInterval I) (f: I -> ℝ) [Topology.IsContinuous f] :
  ∀{a b: ℝ} (ha: a ∈ I) (hb: b ∈ I),
  ∀k, f ⟨a, ha⟩ ≤ k -> k ≤ f ⟨b, hb⟩ ->
  k ∈ Set.range f := by
  intro a b ha hb
  apply isInterval.range I hI f (Set.mem_range' (x := ⟨a, ha⟩)) (Set.mem_range' (x := ⟨b, hb⟩))

end Real
