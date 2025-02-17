import Math.Order.Lattice.Complete
import Math.Order.GaloisConnection
import Math.Relation.Lattice

open Relation

variable {α: Type*}

instance : LE (Setoid α) where
  le a b := ∀⦃x y⦄, a.r x y -> b.r x y

instance : LT (Setoid α) where
  lt a b := a ≤ b ∧ ¬b ≤ a

def giRelation : @GaloisInsertion (α -> α -> Prop) (Setoid α) _ _ (fun r => setoid (EquivGen r)) (fun s => s.r) where
  gc := by
    intro r s
    dsimp
    apply Iff.intro
    intro h x y g
    exact h (EquivGen.single g)
    intro h x y g
    refine ofMappedEquivGen (s := s.r) (g := ⟨id, h⟩) g
  le_l_u s := by
    apply EquivGen.single

instance : IsPartialOrder (Setoid α) where
  lt_iff_le_and_not_le := Iff.rfl
  le_refl a x y := id
  le_trans ab bc x y a := bc (ab a)
  le_antisymm := by
    intro a b ab ba
    cases a with | mk a aeqv =>
    cases b with | mk b beqv =>
    congr
    ext x y
    apply Iff.intro
    apply ab
    apply ba

instance : CompleteLattice (Setoid α) := giRelation.liftCompleteLattice
