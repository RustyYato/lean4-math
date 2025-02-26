import Math.Function.Basic
import Math.Type.Notation

class IsEmpty (α: Sort*): Prop where
  elim: α -> False

def elim_empty [IsEmpty α] : α -> β := False.elim ∘ IsEmpty.elim

instance : IsEmpty False := ⟨id⟩
instance : IsEmpty PEmpty := ⟨PEmpty.elim⟩
instance : IsEmpty Empty := ⟨Empty.elim⟩
instance {α: Sort*} {β: α -> Sort*} [Inhabited α] [IsEmpty (β default)] : IsEmpty (∀x, β x) where
  elim f := elim_empty (f default)
instance {α: Type*} {β: α -> Type*} [∀x, IsEmpty (β x)] : IsEmpty ((x: α) × β x) where
  elim f := elim_empty f.2
instance {α: Sort*} {β: α -> Sort*} [∀x, IsEmpty (β x)] : IsEmpty ((x: α) ×' β x) where
  elim f := elim_empty f.2
instance {α: Type*} {β: α -> Type*} [IsEmpty α] : IsEmpty ((x: α) × β x) where
  elim f := elim_empty f.1
instance {α: Sort*} {β: α -> Sort*} [IsEmpty α] : IsEmpty ((x: α) ×' β x) where
  elim f := elim_empty f.1
instance {α: Type*} {β: Type*} [IsEmpty α] : IsEmpty (α × β) where
  elim f := elim_empty f.1
instance {α: Sort*} {β: Sort*} [IsEmpty α] : IsEmpty (α ×' β) where
  elim f := elim_empty f.1
instance {α: Type*} {β: Type*} [IsEmpty α] [IsEmpty β] : IsEmpty (α ⊕ β) where
  elim f := (by cases f <;> (rename_i f; exact elim_empty f))
instance {α: Sort*} {β: Sort*} [IsEmpty α] [IsEmpty β] : IsEmpty (α ⊕' β) where
  elim f := (by cases f <;> (rename_i f; exact elim_empty f))
instance {α: Prop} {β: Prop} [IsEmpty α] : IsEmpty (α ∧ β) where
  elim f := elim_empty f.1
instance {α: Prop} {β: Prop} [IsEmpty β] : IsEmpty (α ∧ β) where
  elim f := elim_empty f.2
instance {α: Prop} {β: Prop} [IsEmpty α] [IsEmpty β] : IsEmpty (α ∨ β) where
  elim f := (by cases f <;> (rename_i f; exact elim_empty f))
instance {α: Type*} [IsEmpty α] : IsEmpty (ULift α) where
  elim f := (by cases f <;> (rename_i f; exact elim_empty f))
instance {α: Sort*} [IsEmpty α] : IsEmpty (PLift α) where
  elim f := (by cases f <;> (rename_i f; exact elim_empty f))
instance : IsEmpty (Fin 0) where
  elim f := f.elim0
def Function.isEmpty (f: α -> β) [IsEmpty β] : IsEmpty α where
  elim x := elim_empty (f x)

def Function.empty [IsEmpty α] : α -> β := elim_empty
def Function.empty_inj [IsEmpty α] {f: α -> β} : Function.Injective f := by
  intro x; exact elim_empty x
def Function.empty_surj [IsEmpty β] {f: α -> β} : Function.Surjective f := by
  intro x; exact elim_empty x
def Function.empty_bij [IsEmpty α] [IsEmpty β] : Function.Bijective (empty (α := α) (β := β)) :=
  ⟨empty_inj, empty_surj⟩

instance [IsEmpty α] : Subsingleton α where
  allEq x := elim_empty x

instance [IsEmpty α] (β: α -> Sort*) : Subsingleton (∀x, β x) where
  allEq f g := by
    funext x
    exact elim_empty x

instance [IsEmpty α] : Subsingleton (α -> β) := inferInstance

def IsEmpty.ofNotNonempty (h: ¬Nonempty α) : IsEmpty α where
  elim x := h ⟨x⟩

instance [IsEmpty α] : Subsingleton (Option α) where
  allEq := by
    intro a b
    cases a; cases b
    rfl
    rename_i x
    exact elim_empty x
    rename_i x
    exact elim_empty x

def empty_or_nonempty {motive: Sort u -> Prop} (empty: ∀t, IsEmpty t -> motive t) (nonempty: ∀t, Nonempty t -> motive t) : ∀t, motive t := by
  intro t
  by_cases h:Nonempty t
  apply nonempty
  assumption
  apply empty
  exact IsEmpty.ofNotNonempty h

def empty_inj [IsEmpty α] (f: α -> β) : Function.Injective f := fun x => elim_empty x
