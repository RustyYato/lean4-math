import Math.Data.Finset.Basic
import Math.Logic.IsEmpty

class FinsetLike (S: Type*)(α: outParam Type*) where
  coe : S -> Finset α
  coe_inj: Function.Injective coe

attribute [coe] FinsetLike.coe

variable [FinsetLike S α]

instance : CoeTC S (Finset α) where
  coe := FinsetLike.coe

instance : Membership α S where
  mem s x := x ∈ (s: Finset α)
instance : HasSubset S where
  Subset a b := ∀x ∈ a, x ∈ b

@[coe]
def FinsetLike.Elem [FinsetLike S α] (s: S) := { x : α // x ∈ s }

instance  (priority := 100) : CoeSort S (Type _) := ⟨FinsetLike.Elem⟩

class IsLawfulEmptyFinsetLike (α: Type*) [h: Inhabited α] [FinsetLike α β] extends IsEmpty h.default where

variable (p q : S)

/-- Note: implementers of `FinsetLike` must copy this lemma in order to tag it with `@[ext]`. -/
def FinsetLike.ext (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
  FinsetLike.coe_inj <| Finset.ext _ _ (fun {_} => h _)

@[simp]
def mem_coe {x : α} : x ∈ (p : Finset α) ↔ x ∈ p :=
  Iff.rfl

instance : FinsetLike (Finset α) α where
  coe := id
  coe_inj _ _ := id
