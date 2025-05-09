import Math.Data.Set.Basic

class SetLike (S: Type*) (α: outParam Type*) where
  coe : S -> Set α := by intro s; exact s.carrier
  coe_inj: Function.Injective coe := by intro a b h; cases a; cases b; congr; try (apply SetLike.coe_inj; assumption)

attribute [coe] SetLike.coe

variable [SetLike S α]

instance : CoeTC S (Set α) where
  coe := SetLike.coe

instance : Membership α S where
  mem s x := x ∈ (s: Set α)
instance : HasSubset S where
  Subset a b := ∀x ∈ a, x ∈ b

@[coe]
def SetLike.Elem [SetLike S α] (s: S) := { x : α // x ∈ s }

instance  (priority := 100) : CoeSort S (Type _) := ⟨SetLike.Elem⟩

class IsLawfulEmptySetLike (α: Type*) [h: Inhabited α] [SetLike α β] extends IsEmpty h.default where

variable (p q : S)

@[simp]
def coe_sort_coe : (p : Set α).Elem = p := rfl

/-- Note: implementers of `SetLike` must copy this lemma in order to tag it with `@[ext]`. -/
def SetLike.ext (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
  SetLike.coe_inj <| Set.ext _ _ h

@[simp]
def mem_coe {x : α} : x ∈ (p : Set α) ↔ x ∈ p :=
  Iff.rfl

instance : SetLike (Set α) α where
  coe := id
  coe_inj _ _ := id

instance [DecidableEq α] [SetLike S α] (s: S) : DecidableEq s :=
  fun a b => decidable_of_iff (a.val = b.val) <| by
    cases a; cases b;
    simp; apply Iff.intro
    rintro rfl; rfl
    intro h; cases h; rfl
