import Math.Order.Monotone.Defs
import Math.Data.Set.Basic

variable [LE α] [LT α] [LE β] [LT β] [LE γ] [LT γ] (f: α -> β) (g: β -> γ)
variable {s t: Set α}

def MonotoneOn (s : Set α) : Prop :=
  ∀⦃x y: α⦄, x ∈ s -> y ∈ s -> x ≤ y -> f x ≤ f y

abbrev AntitoneOn (s : Set α) : Prop :=
  ∀⦃x y: α⦄, x ∈ s -> y ∈ s -> x ≤ y -> f y ≤ f x

def StrictMonotoneOn (s: Set α) := ∀⦃x y: α⦄, x ∈ s -> y ∈ s -> x < y -> f x < f y
abbrev StrictAntitoneOn (s: Set α) := ∀⦃x y: α⦄, x ∈ s -> y ∈ s -> x < y -> f y < f x

variable {f: α -> β} {g: β -> γ}

def MonotoneOn.ofMonotone (m: Monotone f) : MonotoneOn f s := fun _ _ _ _ h => m h

def MonotoneOn.ofSuperset (mf: MonotoneOn f s) (h: t ⊆ s) : MonotoneOn f t :=
  fun _ _ hx hy g => mf (h _ hx) (h _ hy) g

def StrictMonotoneOn.ofSuperset (mf: StrictMonotoneOn f s) (h: t ⊆ s) : StrictMonotoneOn f t :=
  fun _ _ hx hy g => mf (h _ hx) (h _ hy) g

def Monotone.iffOnUniv : MonotoneOn f ⊤ ↔ Monotone f := by
  apply Iff.intro
  intro m x y h
  apply m <;> trivial
  intro m x y _ _
  apply m

def StrictMonotone.iffOnUniv : StrictMonotoneOn f ⊤ ↔ StrictMonotone f := by
  apply Iff.intro
  intro m x y h
  apply m <;> trivial
  intro m x y _ _
  apply m

def antitone_on_iff_monotone_on_opp : AntitoneOn f S ↔ MonotoneOn (Opposite.mk ∘ f) S := Iff.rfl
def strict_antitone_on_iff_strict_monotone_on_opp : StrictAntitoneOn f S ↔ StrictMonotoneOn (Opposite.mk ∘ f) S := Iff.rfl

def monotone_on_iff_antitone_on_opp : MonotoneOn f S ↔ AntitoneOn (Opposite.mk ∘ f) S := Iff.rfl
def strict_monotone_on_iff_strict_antitone_on_opp : StrictMonotoneOn f S ↔ StrictAntitoneOn (Opposite.mk ∘ f) S := Iff.rfl

def StrictMonotoneOn.toMonotoneOn [IsPartialOrder α] [IsPreOrder β] (hf: StrictMonotoneOn f S) : MonotoneOn f S := by
  intro x y hx hy h
  rcases lt_or_eq_of_le h with h | rfl
  apply le_of_lt
  apply hf; assumption
  assumption
  assumption
  rfl

def StrictAntitoneOn.toAntitoneOn [IsPartialOrder α] [IsPreOrder β] (hf: StrictAntitoneOn f S) : AntitoneOn f S := by
  rw [antitone_on_iff_monotone_on_opp]
  apply StrictMonotoneOn.toMonotoneOn
  rw [←strict_antitone_on_iff_strict_monotone_on_opp]
  assumption

def StrictMonotoneOn.le_iff_le [IsLinearOrder α] [IsPreOrder β] (hf : StrictMonotoneOn f S) {a b : α} (ha: a ∈ S) (hb: b ∈ S) : f a ≤ f b ↔ a ≤ b := by
  apply Iff.intro
  intro h
  rw [←not_lt]
  intro g
  exact not_le_of_lt (hf hb ha g) h
  intro h
  apply hf.toMonotoneOn
  repeat assumption
