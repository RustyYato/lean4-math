import Math.Type.Notation
import Math.Data.Opposite

class IsNontrivial (α: Type*): Prop where
  exists_ne: ∃a b: α, a ≠ b

def IsNontrivial.iff_exists_ne :
  IsNontrivial α ↔ ∃a b: α, a ≠ b := by
  apply Iff.intro
  intro ⟨a, b, h⟩
  refine ⟨_, _, h⟩
  intro ⟨a, b, h⟩
  refine ⟨_, _, h⟩

def Subsingleton.iff_forall_eq :
  Subsingleton α ↔ ∀a b: α, a = b := by
  apply Iff.intro
  intro h
  apply h.elim
  exact (⟨·⟩)

def IsNontrivial.iff_not_subsingleton :
  IsNontrivial α ↔ ¬Subsingleton α := by
  rw [Subsingleton.iff_forall_eq, IsNontrivial.iff_exists_ne]
  conv => {
    rhs
    rw [Classical.not_forall]
    arg 1; intro a
    rw [Classical.not_forall]
  }

def Subsingleton.iff_not_nontrivial :
  Subsingleton α ↔ ¬IsNontrivial α := by
  rw [Subsingleton.iff_forall_eq, IsNontrivial.iff_exists_ne]
  conv => {
    rhs
    rw [not_exists]
    intro a
    rw [not_exists]
    intro b
    rw [Classical.not_not]
  }

instance : IsNontrivial Nat where
  exists_ne := ⟨0, 1, by decide⟩

instance : IsNontrivial Int where
  exists_ne := ⟨0, 1, by decide⟩

instance : IsNontrivial Bool where
  exists_ne := ⟨false, true, by decide⟩

instance : IsNontrivial Prop where
  exists_ne := ⟨False, True, by decide⟩

instance [h: IsNontrivial α] : IsNontrivial αᵒᵖ where
  exists_ne := h.exists_ne

def exists_ne [h: IsNontrivial α] (a: α) : ∃b, b ≠ a := by
  obtain ⟨x, y, h⟩ := h
  by_cases g:y = a
  subst a
  exists x
  exists y

def subsingleton_or_nontrivial (α: Type*) : Subsingleton α ∨ IsNontrivial α := by
  apply Classical.or_iff_not_imp_right.mpr
  intro h
  rw [Subsingleton.iff_not_nontrivial]
  assumption
