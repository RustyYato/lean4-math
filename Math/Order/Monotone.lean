import Math.Order.Notation
import Math.Data.Set.Basic

variable [LE α] [LT α] [LE β] [LT β] [LE γ] [LT γ] (f: α -> β) (g: β -> γ)
variable {s t: Set α}

def Monotone := ∀⦃x y: α⦄, x ≤ y -> f x ≤ f y

abbrev Antitone := Monotone (Opposite.mk ∘ f)

def MonotoneOn (s : Set α) : Prop :=
  ∀⦃x y: α⦄, x ∈ s -> y ∈ s -> x ≤ y -> f x ≤ f y

abbrev AntitoneOn (s : Set α) : Prop :=
  MonotoneOn (Opposite.mk ∘ f) s

def StrictMonotone := ∀⦃x y: α⦄, x < y -> f x < f y
abbrev StrictAntitone := StrictMonotone (Opposite.mk ∘ f)

def StrictMonotoneOn (s: Set α) := ∀⦃x y: α⦄, x ∈ s -> y ∈ s -> x < y -> f x < f y
abbrev StrictAntitoneOn (s: Set α) := StrictMonotoneOn (Opposite.mk ∘ f) s

variable {f: α -> β} {g: β -> γ}

@[simp]
def monotone_comp_ofDual_iff : Monotone (Opposite.mk ∘ f) ↔ Antitone f := Iff.rfl

@[simp]
def antitone_comp_ofDual_iff : Antitone (Opposite.mk ∘ f) ↔ Monotone f := Iff.rfl

def Monotone.id : Monotone (fun x: α => x) := fun _ _ => _root_.id
def MonotoneOn.ofMonotone (m: Monotone f) : MonotoneOn f s := fun _ _ _ _ h => m h

def StrictMonotone.id : StrictMonotone (fun x: α => x) := fun _ _ => _root_.id

def StrictMonotone.comp (mf: StrictMonotone f) (mg: StrictMonotone g) : StrictMonotone (g ∘ f) := fun _ _ h => mg (mf h)

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

def Monotone.dual (m: Monotone f) : Monotone (Opposite.mk ∘ f ∘ Opposite.get) := by
  intro x y le
  apply m
  assumption

def Monotone.comp (mg: Monotone g) (mf: Monotone f) : Monotone (g ∘ f) :=
  fun {_ _} h => mg (mf h)
