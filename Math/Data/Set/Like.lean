import Math.Data.Set.Basic

class SetLike (S: Type*) (α: outParam Type*) where
  coe : S -> Set α
  coe_inj: Function.Injective coe

attribute [coe] SetLike.coe

variable [SetLike S α]

instance : CoeTC S (Set α) where
  coe := SetLike.coe

instance : Membership α S where
  mem s x := x ∈ (s: Set α)
instance : HasSubset S where
  Subset a b := ∀x ∈ a, x ∈ b

instance  (priority := 100) : CoeSort S (Type _) :=
  ⟨fun s => { x : α // x ∈ s }⟩

class IsLawfulEmptySetLike (α: Type*) [h: Inhabited α] [SetLike α β] extends IsEmpty h.default where

variable (p q : S)

@[simp]
theorem coe_sort_coe : (p : Set α).Elem = p := rfl

/-- Note: implementers of `SetLike` must copy this lemma in order to tag it with `@[ext]`. -/
def ext (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
  SetLike.coe_inj <| Set.ext _ _ h

@[simp]
theorem mem_coe {x : α} : x ∈ (p : Set α) ↔ x ∈ p :=
  Iff.rfl

instance : SetLike (Set α) α where
  coe := id
  coe_inj _ _ := id
