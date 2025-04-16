import Math.Data.Finset.Like
import Math.Data.Finset.Lattice
import Math.Order.Defs

section
-- we seperate out the necessary parts to define DFinsupp here
-- so we that we don't require DecidableEq to just mention DFinsupp
class FiniteSupportOps (S ι: Type*) extends Inhabited S, FinsetLike S ι where
  mem_spec (s: S) (i: ι): i ∈ s ↔ i ∈ (s: Finset ι)
  all (s: S): (ι -> Bool) -> Bool
  all_spec (s: S) (f: ι -> Bool) : (∀x ∈ s, f x) ↔ all s f = true

class FiniteSupport (S: Type*) (ι: outParam Type*) extends
  FiniteSupportOps S ι, LatticeOps S, IsLattice S where
  singleton: ι -> S
  mem_singleton: ∀i, i ∈ singleton i
  remove: ι -> S -> S
  mem_remove:  ∀(s: S) (x i: ι), x ∈ s -> i ≠ x -> x ∈ remove i s
  le_spec {a b: S}: a ≤ b ↔ (a: Finset ι) ⊆ (b: Finset ι)
  mem_min: ∀{a b: S} {x}, x ∈ a -> x ∈ b -> x ∈ a ⊓ b

instance : FiniteSupportOps (Finset ι) ι where
  mem_spec _ _ := Iff.rfl
  all s f := ∀x ∈ s, f x
  all_spec s f := by simp

instance [DecidableEq ι] : FiniteSupport (Finset ι) ι where
  singleton := ({·})
  mem_singleton _ := Finset.mem_singleton.mpr rfl
  remove := Finset.erase
  mem_remove := by
    intro s x i hx ne
    apply Finset.mem_erase.mpr
    apply And.intro hx
    symm; assumption
  le_spec := Iff.rfl
  mem_min := by
    intro a b x ha hb
    apply Finset.mem_inter.mpr
    apply And.intro <;> assumption

instance : FiniteSupportOps Nat Nat where
  mem_spec _ _ := Iff.rfl
  all n f := ∀x < n, f x
  all_spec n f := by
    simp [Nat.mem_iff_lt]

instance : FiniteSupport Nat Nat where
  singleton := (· + 1)
  mem_singleton _ := by rw [Nat.mem_iff_lt]; apply Nat.lt_succ_self
  remove i s := if i + 1 = s then i else s
  mem_remove := by
    intro s x i hx ne
    simp [Nat.mem_iff_lt] at*
    split
    subst s; apply lt_of_le_of_ne
    apply Nat.le_of_lt_succ; assumption
    symm; assumption
    assumption
  le_spec {a b} := by
    simp [HasSubset.Subset, Nat.mem_iff_lt]
    apply Iff.intro
    intro h x g; apply lt_of_lt_of_le
    assumption
    assumption
    intro h; rw [←not_lt]
    intro g
    exact lt_irrefl (h _ g)
  mem_min := by
    intro a b x ha hb
    simp [Nat.mem_iff_lt] at *
    omega

end

namespace FiniteSupport

variable [FiniteSupport S ι] [DecidableEq ι]

def coe_max_sub_max_coe (a b: S) : (a ⊔ b: Finset ι) ≤ ((a ⊔ b: S): Finset ι) := by
  apply max_le
  apply FiniteSupport.le_spec.mp
  apply le_max_left
  apply FiniteSupport.le_spec.mp
  apply le_max_right

def min_coe_sub_coe_min (a b: S) : ((a ⊓ b: S): Finset ι) ≤ (a ⊓ b: Finset ι) := by
  apply le_min
  apply FiniteSupport.le_spec.mp
  apply min_le_left
  apply FiniteSupport.le_spec.mp
  apply min_le_right

def mem_max (i: ι) (a b: S) : i ∈ a -> i ∈ a ⊔ b := by
  classical
  intro h
  apply coe_max_sub_max_coe
  apply Finset.mem_union.mpr
  left; assumption

end FiniteSupport
