import Math.Algebra.Group.Theory.Symm
import Math.Algebra.Group.SetLike.Basic

inductive Alternating.Generate [DecidableEq α] : Symm α -> Prop where
| intro (a b c d: α) :
  -- we need to enforce that you don't swap the same element with itself
  -- otherwise this wouldn't represent only even number of swaps
  a ≠ b -> c ≠ d -> Generate ((Equiv.swap a b).trans (Equiv.swap c d))

-- the alternating group is the subgroup of the symmetric group generated
-- by an even number of swaps
instance Alternating (α: Type*) [DecidableEq α] : Subgroup (Symm α) :=
  Subgroup.generate (Set.mk Alternating.Generate)

-- the alternating group of Bool is exactly the unit
instance : Subsingleton (Alternating Bool) where
  allEq := by
    suffices ∀a: Alternating Bool, a = 1 by
      intro a b; rw [this a, this b]
    intro ⟨a, ha⟩; congr
    induction ha with
    | one => rfl
    | mul _ _ ih₀ ih₁ => simp [ih₀, ih₁]
    | inv _ ih => simp [ih]
    | of b h =>
      clear a
      cases h with
      | intro a b c d ab cd =>
      cases a <;> cases b <;> cases c <;> cases d
      any_goals contradiction
      rw (occs := [1]) [Equiv.swap_comm, ←Equiv.swap_symm]
      rw [Equiv.symm_trans]; rfl
      rw [←Equiv.swap_symm false true, Equiv.trans_symm]; rfl
      rw [←Equiv.swap_symm true false, Equiv.trans_symm]; rfl
      rw (occs := [1]) [Equiv.swap_comm, ←Equiv.swap_symm]
      rw [Equiv.symm_trans]; rfl

-- the alternating group over a set of two elements is equivalent to the trivial group
def alt2_eqv_trivial : Alternating Bool ≃* Group.Trivial :=
  Group.eqv_trivial (Alternating Bool)
