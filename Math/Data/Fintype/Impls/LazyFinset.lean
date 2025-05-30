import Math.Data.LazyFinset.Basic
import Math.Data.Fintype.Impls.Finset
import Math.Data.Set.Defs

instance [DecidableEq α] (s: LazyFinset α) : Fintype s :=
  Fintype.ofEquiv (β := Equiv.lazy_finset_eqv_finset s) (Equiv.congrSubtype .rfl (by
    intro x
    simp [Equiv.lazy_finset_eqv_finset]
    show x ∈ s ↔ x ∈ s.toMultiset
    simp))

def LazyFinset.univ (α: Type*) [f: Fintype α] : LazyFinset α :=
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

def LazyFinset.mem_univ (α: Type*) [f: Fintype α] : ∀x, x ∈ univ α := by
  induction f using Fintype.ind with | _ r =>
  intro x
  apply List.mem_ofFn.mpr
  have ⟨i, h⟩ := r.bij.Surjective x
  exists i; symm; assumption

instance [Fintype α] [DecidableEq α] : SetComplement (LazyFinset α) where
  scompl s := LazyFinset.univ α \ s

def LazyFinset.mem_compl [Fintype α] [DecidableEq α] {s: LazyFinset α} : ∀{x}, x ∈ sᶜ ↔ x ∉ s := by
  intro x
  show x ∈ LazyFinset.univ α \ s ↔ _
  simp [LazyFinset.mem_sdiff, LazyFinset.mem_univ]

def LazyFinset.compl_compl [Fintype α] [DecidableEq α] (s: LazyFinset α) : sᶜᶜ = s := by
  ext; simp [mem_compl]
