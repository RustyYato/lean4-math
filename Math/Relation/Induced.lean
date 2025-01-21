import Math.Relation.RelIso
import Math.Data.Set.Basic

def Subtype.inducedRelation (f: α -> β) (r: α -> α -> Prop) (a b: Subtype (· ∈ Set.range f)) : Prop :=
  ∃x y: α, r x y ∧ a = f x ∧ b = f y

noncomputable
def Subtype.inducedEquiv (f: α ↪ β) (r: α -> α -> Prop) : r ≃r Subtype.inducedRelation f r where
  toFun a := ⟨f a, Set.mem_range'⟩
  invFun x := Classical.choose x.property
  leftInv := by
    intro x
    dsimp
    apply f.inj
    show f _ = f _
    have : f x ∈ Set.range f := Set.mem_range'
    rw [←Classical.choose_spec this]
  rightInv := by
    intro ⟨x, hx⟩
    dsimp
    congr
    rw [←Classical.choose_spec hx]
  resp_rel := by
    dsimp
    intro x y
    apply Iff.intro
    intro h
    refine ⟨x, y, ?_, ?_, ?_⟩
    assumption
    rfl
    rfl
    intro ⟨x₀, x₁, h, eq₀, eq₁⟩
    dsimp at eq₀ eq₁
    cases f.inj eq₀
    cases f.inj eq₁
    assumption

instance (f: α ↪ β) (r: α -> α -> Prop) [Relation.IsWellOrder r] :
  Relation.IsWellOrder (Subtype.inducedRelation f r) :=
  (Subtype.inducedEquiv f r).symm.toRelEmbedding.wo
