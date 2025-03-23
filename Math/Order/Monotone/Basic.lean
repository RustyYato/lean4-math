import Math.Order.Monotone.Defs
import Math.Data.Set.Basic

variable [LE α] [LT α] [LE β] [LT β] [LE γ] [LT γ] (f: α -> β) (g: β -> γ)
variable {s t: Set α}

def MonotoneOn (s : Set α) : Prop :=
  ∀⦃x y: α⦄, x ∈ s -> y ∈ s -> x ≤ y -> f x ≤ f y

abbrev AntitoneOn (s : Set α) : Prop :=
  MonotoneOn (Opposite.mk ∘ f) s

def StrictMonotoneOn (s: Set α) := ∀⦃x y: α⦄, x ∈ s -> y ∈ s -> x < y -> f x < f y
abbrev StrictAntitoneOn (s: Set α) := StrictMonotoneOn (Opposite.mk ∘ f) s

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
