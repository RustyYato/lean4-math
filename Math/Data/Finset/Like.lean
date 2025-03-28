import Math.Data.Finset.Basic
import Math.Logic.IsEmpty

class FinsetLike (S: Type*) (α: outParam Type*) where
  coe : S -> Finset α
  coe_inj: Function.Injective coe

attribute [coe] FinsetLike.coe

variable [FinsetLike S α]

namespace FinsetLike

instance : CoeTC S (Finset α) where
  coe := FinsetLike.coe

instance : Membership α S where
  mem s x := x ∈ (s: Finset α)
instance : HasSubset S where
  Subset a b := ∀x ∈ a, x ∈ b

@[coe]
def Elem [FinsetLike S α] (s: S) := { x : α // x ∈ s }

instance  (priority := 100) : CoeSort S (Type _) := ⟨FinsetLike.Elem⟩

end FinsetLike


class IsLawfulEmptyFinsetLike (α: Type*) [h: Inhabited α] [FinsetLike α β] extends IsEmpty h.default where

variable (p q : S)

/-- Note: implementers of `FinsetLike` must copy this lemma in order to tag it with `@[ext]`. -/
def FinsetLike.ext (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
  FinsetLike.coe_inj <| Finset.ext _ _ (fun {_} => h _)

@[simp]
def mem_coe_finset {x : α} : x ∈ (p : Finset α) ↔ x ∈ p :=
  Iff.rfl

instance : FinsetLike (Finset α) α where
  coe := id
  coe_inj _ _ := id

instance : IsLawfulEmptyFinsetLike (Finset α) where
  elim x := Finset.not_mem_empty _ x.property

instance : FinsetLike Nat Nat where
  coe n := {
    val := Multiset.mk (List.ofFn (n := n) Fin.val)
    property := by
      apply (List.nodup_ofFn _).mp
      intro x y
      apply Fin.val_inj.mp
  }
  coe_inj := by
    intro a b eq
    dsimp at eq
    replace eq := Quotient.exact (Subtype.mk.inj eq)
    rcases Nat.lt_trichotomy a b with lt | rfl | gt
    · have : a ∈ List.ofFn (n := b) Fin.val := by
        refine (List.mem_ofFn _ _).mpr ?_
        exists ⟨a, lt⟩
      have := (List.Perm.mem_iff eq).mpr this
      simp at this
      obtain ⟨⟨_, lt⟩, eq⟩ := this
      dsimp at eq
      subst eq
      have := Nat.lt_irrefl _ lt
      contradiction
    · rfl
    · have : b ∈ List.ofFn (n := a) Fin.val := by
        refine (List.mem_ofFn _ _).mpr ?_
        exists ⟨b, gt⟩
      have := (List.Perm.mem_iff eq).mp this
      simp at this
      obtain ⟨⟨_, lt⟩, eq⟩ := this
      dsimp at eq
      subst eq
      have := Nat.lt_irrefl _ lt
      contradiction

instance : IsLawfulEmptyFinsetLike Nat where
  elim x := by
    have : x.val ∈ (0: Nat) := x.property
    contradiction

def Nat.mem_iff_lt (a b: Nat) : a ∈ b ↔ a < b := by
  apply Iff.trans (List.mem_ofFn _ _)
  apply Iff.intro
  intro ⟨⟨i, _⟩, h⟩
  dsimp at h; subst h
  assumption
  intro h
  exact ⟨⟨a, h⟩, rfl⟩

instance (a b: Nat) : Decidable (a ∈ b) :=
  decidable_of_iff _ (Nat.mem_iff_lt _ _).symm

-- this isn't possible to do, since the coercion isn't injective because zip is degenerate
-- if either input is empty
-- instance [FinsetLike α α₀] [FinsetLike β β₀] : FinsetLike (α × β) (α₀ × β₀) where
--   coe x := (x.1: Finset α₀).zip (x.2: Finset β₀)
--   coe_inj := by
--     intro x y eq
--     dsimp at eq
--     sorry
