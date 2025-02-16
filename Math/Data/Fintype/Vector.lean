import Math.Data.Fintype.Defs
import Math.Data.Vector.Basic

private def all (f: Fintype α) : ∀n, List (List.Vector α n)
| 0 => [.nil _]
| n + 1 => (all f n).flatMap <| fun as => f.all.map <| fun a => as.cons a

instance [Fintype α] : Fintype (List.Vector α n) where
  all := all inferInstance n
  nodup := by
    induction n with
    | zero =>
      apply List.Pairwise.cons
      intro _ _; contradiction
      apply List.Pairwise.nil
    | succ n ih =>
      unfold all
      apply List.nodup_flatMap
      assumption
      intro x
      apply List.nodup_map
      intro x y eq
      dsimp at eq
      cases eq
      rfl
      apply Fintype.nodup
      intro as bs ha hb z hz₀ hz₁
      rw [List.mem_map] at hz₀ hz₁
      obtain ⟨_, _, hz₀⟩ := hz₀
      obtain ⟨_, _, hz₁⟩ := hz₁
      have := hz₀.trans hz₁.symm
      match as with
      | .mk as _ =>
      match bs with
      | .mk bs _ =>
      cases this
      rfl
  complete := by
    intro x
    induction x with
    | nil =>
      apply List.Mem.head
    | cons a as ih =>
      rw [all]
      simp [List.mem_flatMap, List.mem_map]
      exists as
      apply And.intro
      assumption
      exists a
      apply And.intro
      apply Fintype.complete
      rfl
