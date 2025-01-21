import Math.Type.Notation

namespace Function

variable (g: β -> α) (f: α -> β)
variable {g₀ g₁: β -> α} {f₀ f₁: α -> β}

@[reducible]
def Injective: Prop := ∀⦃x y⦄, f x = f y -> x = y
@[reducible]
def Surjective: Prop := ∀b, ∃a, f a = b
@[reducible]
def Bijective: Prop := Injective f ∧ Surjective f
@[reducible]
def Injective₂ (f: α₀ -> α₁ -> β): Prop := ∀⦃x₀ x₁ y₀ y₁⦄, f x₀ x₁ = f y₀ y₁ -> x₀ = y₀ ∧ x₁ = y₁

def IsLeftInverse: Prop := ∀x, g (f x) = x
def IsRightInverse: Prop := ∀x, f (g x) = x

variable {g: β -> α} {f: α -> β}

def Bijective.Injective : Bijective f -> Injective f := And.left
def Bijective.Surjective : Bijective f -> Surjective f := And.right

def Surjective.exists_inv : Surjective f -> ∃g: β -> α, ∀x, f (g x) = x :=
  Classical.axiomOfChoice

def Injective.comp {f: α₀ -> α₁} {g: α₁ -> α₂} : Function.Injective g ->  Function.Injective f -> Function.Injective (g ∘ f) := by
  intro ginj finj x y eq
  apply finj
  apply ginj
  assumption

def Injective.eq_iff : Function.Injective f₀ -> (∀{x y}, f₀ x = f₀ y ↔ x = y) := by
  intro inj x y
  apply Iff.intro
  intro h
  exact inj h
  intro h
  rw [h]

theorem Injective.of_comp {g : γ → α} (I : Injective (f ∘ g)) : Injective g :=
  fun _ _ h ↦ I <| congrArg f h

def Injective.of_comp_iff (hf : Injective f) (g : γ → α) :
    Injective (f ∘ g) ↔ Injective g :=
  ⟨Injective.of_comp, (hf.comp ·)⟩

def HasLeftInverse: Prop := ∃g, IsLeftInverse g f
def HasRightInverse: Prop := ∃g, IsRightInverse g f

def IsLeftInverse.Injective : IsLeftInverse g f -> Injective f := by
  intro inv x y eq
  rw [←inv x, ←inv y, eq]

def IsRightInverse.Injective : IsRightInverse g f -> Injective g := IsLeftInverse.Injective

def IsRightInverse.Surjective : IsRightInverse g f -> Surjective f := by
  intro h x
  exists g x
  rw [h]

def IsLeftInverse.Surjective : IsLeftInverse g f -> Surjective g := IsRightInverse.Surjective

def IsLeftInverse.comp_id_eq : IsLeftInverse g f -> g ∘ f = id := by
  intro h
  funext x
  dsimp
  rw [h]

def IsRightInverse.comp_id_eq : IsRightInverse g f -> f ∘ g = id := by
  intro h
  funext x
  dsimp
  rw [h]

def comp_id (f: α -> β) : f ∘ id = f := rfl
def id_comp (f: α -> β) : id ∘ f = f := rfl
def comp_assoc (a₀: α₀ -> α₁) (a₁: α₁ -> α₂) (a₂: α₂ -> α₃) :
  a₂ ∘ a₁ ∘ a₀ = (a₂ ∘ a₁) ∘ a₀ := rfl

def inverse_congr : IsLeftInverse g₀ f₀ -> IsRightInverse g₁ f₀ -> g₀ = g₁ := by
  intro a b
  rw [←comp_id g₀, ←b.comp_id_eq, comp_assoc, a.comp_id_eq, id_comp]

def hfunext {α α' : Sort u} {β : α → Sort v} {β' : α' → Sort v} {f : ∀a, β a} {f' : ∀a, β' a}
    (hα : α = α') (h : ∀a a', HEq a a' → HEq (f a) (f' a')) : HEq f f' := by
  subst hα
  have : ∀a, HEq (f a) (f' a) := fun a ↦ h a a (HEq.refl a)
  have : β = β' := by funext a; exact type_eq_of_heq (this a)
  subst this
  apply heq_of_eq
  funext a
  exact eq_of_heq (this a)

open Classical in
noncomputable def invFun {α : Sort u} {β} [Nonempty α] (f : α → β) : β → α :=
  fun y => if h:(∃ x, f x = y) then Classical.choose h else Classical.choice inferInstance

def invFun_eq (h : ∃ a, f a = b) :
  have := nonempty_of_exists h
  f (invFun f b) = b := by
  simp only [invFun, dif_pos h, h.choose_spec]

def apply_invFun_apply {α β : Sort*} {f : α → β} {a : α} :
    f (@invFun _ _ ⟨a⟩ f (f a)) = f a := invFun_eq ⟨_, rfl⟩

def leftinverse_of_invFun [Nonempty α] {f: α -> β} (hf: Injective f) : IsLeftInverse (invFun f) f := by
  intro x
  apply hf
  exact apply_invFun_apply (α := α) (f := f) (a := x)

def IsLeftInverse.comp_eq_id (h: IsLeftInverse f g) : f ∘ g = id := by
  ext x
  apply h

end Function
