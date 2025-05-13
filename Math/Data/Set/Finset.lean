import Math.Data.Set.Finite
import Math.Data.Finset.Basic

def Set.exists_equiv_finset (s: Set α) (h: s.IsFinite) : ∃f: Finset α, ∀x, x ∈ s ↔ x ∈ f := by
  apply IsFinite.induction s
  case nil =>
      exists ∅
      intro x
      simp [Finset.not_mem_empty]
  case cons =>
    intro a s a_notin_s s_finite ih
    replace ih := ih
    obtain ⟨f, h⟩ := ih
    exists f.insert_unique a ?_
    rwa [←h]
    intro x
    simp [Finset.mem_insert_unique, h]

noncomputable def Set.toFinset (s: Set α) (h: s.IsFinite) : Finset α :=
  Classical.choose (Set.exists_equiv_finset s h)

noncomputable def Set.mem_toFinset {s: Set α} {h: s.IsFinite} : ∀{x}, x ∈ s.toFinset h ↔ x ∈ s :=
  fun {x} => (Classical.choose_spec (Set.exists_equiv_finset s h) x).symm
