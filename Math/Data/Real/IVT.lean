import Math.Data.Real.MetricSpace
import Math.Data.Real.Dedekind

open Topology

namespace Real

def intermediate_value_univ₂ {a b : ℝ} {f g : ℝ → ℝ} (hf : IsContinuous f)
  (hg : IsContinuous g) (ha : f a ≤ g a) (hb : g b ≤ f b) : ∃ x, f x = g x := by
  obtain ⟨x, _, hfg, hgf⟩ : (⊤ ∩ Set.mk (fun x => f x ≤ g x ∧ g x ≤ f x)).Nonempty :=
    IsPreconnectedOn.closed_iff.1 IsPreconnected.univ_preconnected _ _ (isClosed_le f g) (isClosed_le g f) (fun _ _ => le_total (α := ℝ) _ _) ⟨a, trivial, ha⟩ ⟨b, trivial, hb⟩
  exact ⟨x, le_antisymm hfg hgf⟩

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
