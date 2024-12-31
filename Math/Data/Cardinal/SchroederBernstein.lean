import Math.Type.Basic
import Math.Data.Set.Basic
import Math.Function.Basic

namespace Embedding

section antisymm

open Classical in
theorem schroeder_bernstein {f : α → β} {g : β → α} (hf : Function.Injective f)
  (hg : Function.Injective g) : ∃ h : α → β, h.Bijective := by
  sorry

theorem antisymm : (α ↪ β) → (β ↪ α) → Nonempty (α ≃ β)
  | ⟨_, h₁⟩, ⟨_, h₂⟩ =>
    let ⟨_, hf⟩ := schroeder_bernstein h₁ h₂
    have ⟨eqv, _⟩  := Equiv.ofBij hf
    ⟨eqv⟩

end antisymm

section Wo

variable {ι : Type u} (β : ι → Type v)

/-- `sets β` -/
private abbrev sets :=
  Set.mk fun s : Set (∀ i, β i) => ∀ x ∈ s, ∀ y ∈ s, ∀ (i), (x : ∀ i, β i) i = y i → x = y

open Classical in
def min_injective [I : Nonempty ι] : ∃ i, Nonempty (∀ j, β i ↪ β j) :=
  let ⟨s, hs, ms⟩ :=
    show ∃ s ∈ sets β, ∀ a ∈ sets β, s ⊆ a → a = s from
      zorn_subset (sets β) fun c hc hcc =>
        ⟨⋃ c, fun x ⟨p, hpc, hxp⟩ y ⟨q, hqc, hyq⟩ i hi =>
          (hcc.total hpc hqc).elim (fun h => hc hqc x (h hxp) y hyq i hi) fun h =>
            hc hpc x hxp y (h hyq) i hi,
          fun _ => subset_sUnion_of_mem⟩
  let ⟨i, e⟩ :=
    show ∃ i, ∀ y, ∃ x ∈ s, (x : ∀ i, β i) i = y from
      Classical.byContradiction fun h =>
        have h : ∀ i, ∃ y, ∀ x ∈ s, (x : ∀ i, β i) i ≠ y := by
          simpa only [ne_eq, not_exists, not_forall, not_and] using h
        let ⟨f, hf⟩ := Classical.axiomOfChoice h
        have : f ∈ s := by
          have : insert f s ∈ sets β := fun x hx y hy => by
            rcases hx with hx | hx <;> rcases hy with hy | hy;
            · simp [Set.mem_singleton.mp hx, Set.mem_singleton.mp hy]
            · subst x
              exact fun i e => (hf i y hy e.symm).elim
            · subst y
              exact fun i e => (hf i x hx e).elim
            · exact hs x hx y hy
          rw [←ms _ this, Set.mem_insert]
          exact .inl rfl
          intro x h
          exact Set.mem_insert.mpr (.inr h)
        let ⟨i⟩ := I
        hf i f this rfl
  let ⟨f, hf⟩ := Classical.axiomOfChoice e
  ⟨i,
    ⟨fun j =>
      ⟨fun a => f a j, fun a b e' => by
        let ⟨sa, ea⟩ := hf a
        let ⟨sb, eb⟩ := hf b
        rw [← ea, ← eb, hs _ sa _ sb _ e']⟩⟩⟩

end Wo

/-- The cardinals are totally ordered. See
`Cardinal.conditionallyCompleteLinearOrderBot` for (one of) the lattice
instance. -/
-- Porting note: `ULift.{max u v, u} α` was `ULift α`
theorem total (α : Type u) (β : Type v) : Nonempty (α ↪ β) ∨ Nonempty (β ↪ α) :=
  match @min_injective Bool (fun b => cond b (ULift.{max u v, u} α) (ULift.{max u v, v} β)) ⟨true⟩
    with
  | ⟨true, ⟨h⟩⟩ =>
    let ⟨f, hf⟩ := h false
    Or.inl ⟨Embedding.congr Equiv.ulift Equiv.ulift ⟨f, hf⟩⟩
  | ⟨false, ⟨h⟩⟩ =>
    let ⟨f, hf⟩ := h true
    Or.inr ⟨Embedding.congr Equiv.ulift Equiv.ulift ⟨f, hf⟩⟩

end Embedding
