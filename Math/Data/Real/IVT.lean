import Math.Data.Real.MetricSpace
import Math.Topology.IVT

open Topology

namespace Real

def intermediate_value (f: ℝ -> ℝ) (hf: IsContinuous f): Set.Icc (f a) (f b) ⊆ Set.range f := by
  intro x hx
  rw [Set.mem_Icc] at hx
  obtain ⟨fa_le_x, x_le_fb⟩ := hx
  have ⟨y, _⟩ := intermediate_value_univ₂ hf (IsContinuous.const x) fa_le_x x_le_fb
  exists y; symm; assumption

def has_root (f: ℝ -> ℝ) (hf: IsContinuous f): (∃x, f x ≤ 0) -> (∃x, 0 ≤ f x) -> ∃x, f x = 0 := by
  intro ⟨a, ha⟩ ⟨b, hb⟩
  have ⟨x, _⟩ := intermediate_value f hf (a := a) (b := b) 0 ?_
  exists x; symm; assumption
  rw [Set.mem_Icc]
  apply And.intro <;> assumption

end Real
