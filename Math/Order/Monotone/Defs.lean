import Math.Order.Notation

variable [LE α] [LT α] [LE β] [LT β] [LE γ] [LT γ] (f: α -> β) (g: β -> γ)

def Monotone := ∀⦃x y: α⦄, x ≤ y -> f x ≤ f y

abbrev Antitone := Monotone (Opposite.mk ∘ f)

def StrictMonotone := ∀⦃x y: α⦄, x < y -> f x < f y
abbrev StrictAntitone := StrictMonotone (Opposite.mk ∘ f)

variable {f: α -> β} {g: β -> γ}

@[simp]
def monotone_comp_ofDual_iff : Monotone (Opposite.mk ∘ f) ↔ Antitone f := Iff.rfl

@[simp]
def antitone_comp_ofDual_iff : Antitone (Opposite.mk ∘ f) ↔ Monotone f := Iff.rfl

def Monotone.id : Monotone (fun x: α => x) := fun _ _ => _root_.id

def StrictMonotone.id : StrictMonotone (fun x: α => x) := fun _ _ => _root_.id

def StrictMonotone.comp (mf: StrictMonotone f) (mg: StrictMonotone g) : StrictMonotone (g ∘ f) := fun _ _ h => mg (mf h)

def Monotone.dual (m: Monotone f) : Monotone (Opposite.mk ∘ f ∘ Opposite.get) := by
  intro x y le
  apply m
  assumption

def Monotone.comp (mg: Monotone g) (mf: Monotone f) : Monotone (g ∘ f) :=
  fun {_ _} h => mg (mf h)
