import Math.Data.LazyFinset.Defs
import Math.Data.Fintype.Defs
import Math.Data.Set.Defs

def Finset.univ (α: Type*) [f: Fintype α] : LazyFinset α :=
  f.toRepr.lift (fun s => LazyFinset.ofMultiset (Multiset.mk (List.ofFn s.decode))) <| by
    intro a b
    simp
    ext x
    simp
    apply Iff.intro
    · rintro _
      have ⟨i, h⟩ := b.bij.Surjective x
      exact ⟨_, h.symm⟩
    · rintro _
      have ⟨i, h⟩ := a.bij.Surjective x
      exact ⟨_, h.symm⟩

def Finset.mem_univ (α: Type*) [f: Fintype α] : ∀x, x ∈ univ α := by
  induction f using Fintype.ind with | _ r =>
  intro x
  apply List.mem_ofFn.mpr
  have ⟨i, h⟩ := r.bij.Surjective x
  exists i; symm; assumption

-- instance [Fintype α] [DecidableEq α] : SetComplement (LazyFinset α) where
--   scompl s := Finset.univ α \ s

-- def Finset.mem_compl [Fintype α] [DecidableEq α] {s: LazyFinset α} : ∀{x}, x ∈ sᶜ ↔ x ∉ s := by
--   intro x
--   show x ∈ Finset.univ α \ s ↔ _
--   simp [Finset.mem_sdiff, Finset.mem_univ]

-- def Finset.compl_compl [Fintype α] [DecidableEq α] (s: LazyFinset α) : sᶜᶜ = s := by
--   ext; simp [mem_compl]
