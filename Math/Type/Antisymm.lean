import Math.Data.Set.Lattice
import Math.Order.OrderIso
import Math.Order.FixedPoints

variable {α β: Type*}

/-- **The Schröder-Bernstein Theorem**:
Given injections `α → β` and `β → α`, we can get a bijection `α → β`. -/
theorem schroeder_bernstein
  {f : α → β} {g : β → α} (hf : Function.Injective f) (hg : Function.Injective g):
  ∃h: α → β, Function.Bijective h := by
  -- taken straight from mathlib4
  classical

  cases β using empty_or_nonempty <;> rename_i hβ
  · have : IsEmpty α := Function.isEmpty f
    exact ⟨Function.empty, Function.empty_bij⟩

  let F : Set α →≤ Set α :=
    { toFun := fun s => ((s.image f)ᶜ.image g)ᶜ
      monotone := by
        intro s t hst
        dsimp
        apply Set.compl_subset_compl.mpr
        apply Set.image_subset
        apply Set.compl_subset_compl.mpr
        apply Set.image_subset
        assumption}

  -- set S is all the fixed points of F
  let s : Set α := MonotoneHom.lfp F

  have hs : ((s.image f)ᶜ.image g)ᶜ = s := F.map_lfp
  have hns : (s.image f)ᶜ.image g = sᶜ := Set.compl_inj (by simp [hs, Set.compl_compl])
  let g' := Function.invFun g
  have g'g : Function.IsLeftInverse g' g := Function.leftinverse_of_invFun hg
  have hg'ns : sᶜ.image g' = (s.image f)ᶜ := by rw [← hns,
    Set.image_image, g'g.comp_eq_id, Set.image_id]
  let h : α → β := s.piecewise f g'

  refine ⟨s.piecewise f g', ?_, ?_⟩
  · intro x y eq
    unfold Set.piecewise at eq
    split at eq <;> split at eq <;> rename_i hx hy
    exact hf eq
    obtain ⟨y',hy', rfl⟩ : y ∈ (s.image f)ᶜ.image g := by rwa [hns]
    rw [g'g _] at eq
    have := hy' ⟨x, hx, eq.symm⟩
    contradiction

    obtain ⟨x',hx', rfl⟩ : x ∈ (s.image f)ᶜ.image g := by rwa [hns]
    rw [g'g _] at eq
    have := hx' ⟨y, hy, eq⟩
    contradiction

    obtain ⟨x',hx', rfl⟩ : x ∈ (s.image f)ᶜ.image g := by rwa [hns]
    obtain ⟨y',hy', rfl⟩ : y ∈ (s.image f)ᶜ.image g := by rwa [hns]
    rw [g'g, g'g] at eq
    rw [eq]
  · rw [←Set.range_iff_surjective, Set.range_piecewise, hg'ns, Set.union_compl]

noncomputable
def Equiv.antisymm (h: α ↪ β) (g: β ↪ α) : α ≃ β :=
  Classical.choice <|
  have ⟨_, bij⟩  := schroeder_bernstein h.inj g.inj
  nonempty_of_exists (Equiv.ofBij bij)

-- section Wo

-- variable {ι : Type u} (β : ι → Type v)

-- /-- `sets β` -/
-- private abbrev sets :=
--   { s : Set (∀ i, β i) | ∀ x ∈ s, ∀ y ∈ s, ∀ (i), (x : ∀ i, β i) i = y i → x = y }

-- /-- The cardinals are well-ordered. We express it here by the fact that in any set of cardinals
-- there is an element that injects into the others.
-- See `Cardinal.conditionallyCompleteLinearOrderBot` for (one of) the lattice instances. -/
-- theorem min_injective [I : Nonempty ι] : ∃ i, Nonempty (∀ j, β i ↪ β j) := sorry

-- end Embedding

-- end Function
