import Math.Order.Defs
import Math.Function.Basic

variable [LE α] [LT α] [LE β] [LT β] [LE γ] [LT γ] (f: α -> β) (g: β -> γ)

def Monotone := ∀⦃x y: α⦄, x ≤ y -> f x ≤ f y

abbrev Antitone := ∀⦃x y: α⦄, x ≤ y -> f y ≤ f x

def StrictMonotone := ∀⦃x y: α⦄, x < y -> f x < f y
abbrev StrictAntitone := ∀⦃x y: α⦄, x < y -> f y < f x

variable {f: α -> β} {g: β -> γ}

@[simp]
def monotone_comp_ofDual_iff : Monotone (Opposite.mk ∘ f) ↔ Antitone f := Iff.rfl

@[simp]
def antitone_comp_ofDual_iff : Antitone (Opposite.mk ∘ f) ↔ Monotone f := Iff.rfl

protected def Monotone.id : Monotone (fun x: α => x) := fun _ _ => id

protected def StrictMonotone.id : StrictMonotone (fun x: α => x) := fun _ _ => id

def StrictMonotone.comp (mf: StrictMonotone f) (mg: StrictMonotone g) : StrictMonotone (g ∘ f) := fun _ _ h => mg (mf h)

def Monotone.dual (m: Monotone f) : Monotone (Opposite.mk ∘ f ∘ Opposite.get) := by
  intro x y le
  apply m
  assumption

def Monotone.comp (mg: Monotone g) (mf: Monotone f) : Monotone (g ∘ f) :=
  fun {_ _} h => mg (mf h)

def antitone_iff_monotone_opp : Antitone f ↔ Monotone (Opposite.mk ∘ f) := Iff.rfl
def strict_antitone_iff_strict_monotone_opp : StrictAntitone f ↔ StrictMonotone (Opposite.mk ∘ f) := Iff.rfl

def monotone_iff_antitone_opp : Monotone f ↔ Antitone (Opposite.mk ∘ f) := Iff.rfl
def strict_monotone_iff_strict_antitone_opp : StrictMonotone f ↔ StrictAntitone (Opposite.mk ∘ f) := Iff.rfl

def StrictMonotone.toMonotone [IsPartialOrder α] [IsPreOrder β] (hf: StrictMonotone f) : Monotone f := by
  intro x y h
  rcases lt_or_eq_of_le h with h | rfl
  apply le_of_lt
  apply hf; assumption
  rfl

def StrictAntitone.toAntitone [IsPartialOrder α] [IsPreOrder β] (hf: StrictAntitone f) : Antitone f := by
  rw [antitone_iff_monotone_opp]
  apply StrictMonotone.toMonotone
  rw [←strict_antitone_iff_strict_monotone_opp]
  assumption

def StrictMonotone.le_iff_le [IsLinearOrder α] [IsPreOrder β] (hf : StrictMonotone f) {a b : α} : f a ≤ f b ↔ a ≤ b := by
  apply Iff.intro
  intro h
  rw [←not_lt]
  intro g
  exact not_le_of_lt (hf g) h
  intro h
  apply hf.toMonotone
  assumption

def StrictAntitone.le_iff_le [IsLinearOrder α] [IsPreOrder β] (hf : StrictAntitone f) {a b : α} : f a ≤ f b ↔ b ≤ a := by
  rw [strict_antitone_iff_strict_monotone_opp] at hf
  apply hf.le_iff_le

protected def StrictMonotone.Injective [IsLinearOrder α] [IsPreOrder β] (hf: StrictMonotone f) : Function.Injective f := by
  intro x y h
  rcases lt_trichotomy x y with g | g | g
  · have := hf g
    rw [h] at this
    have := lt_irrefl this
    contradiction
  · assumption
  · have := hf g
    rw [h] at this
    have := lt_irrefl this
    contradiction
