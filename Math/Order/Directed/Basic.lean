import Math.Data.Set.Basic

variable {α : Type u} {β : Type v} {ι : Sort w} (r r' s : α → α → Prop)

def Directed (f: ι -> α) := ∀a b, ∃c, r (f a) (f c) ∧ r (f b) (f c)

namespace Set

def DirectedOn (s: Set α) := ∀a ∈ s, ∀b ∈ s, ∃c ∈ s, r a c ∧ r b c

def DirectedOn.iff_directed : DirectedOn r S ↔ Directed r fun x: S => x.val := by
  apply Iff.intro
  intro h a b
  have ⟨c, hc, _, _⟩ := h a.val a.property b.val b.property
  exists ⟨c, hc⟩
  intro h a ha b hb
  have ⟨c, _, _⟩ := h ⟨a, ha⟩ ⟨b, hb⟩
  refine ⟨c, c.property, ?_, ?_⟩ <;> assumption

end Set
