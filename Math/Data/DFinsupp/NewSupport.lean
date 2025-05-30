import Math.Data.LazyFinset.Like
import Math.Data.LazyFinset.Lattice
import Math.Order.Defs

open scoped LazyFinset

section
-- we seperate out the necessary parts to define DFinsupp here
-- so we that we don't require DecidableEq to just mention DFinsupp
class FiniteSupportOps (S ι: Type*) extends Inhabited S, LazyFinsetLike S ι where
  all (s: S): (ι -> Bool) -> Bool
  all_spec (s: S) (f: ι -> Bool) : (∀x ∈ s, f x) ↔ all s f = true

class FiniteSupport (S: Type*) (ι: outParam Type*) extends
  FiniteSupportOps S ι, LE S, LT S, Max S, IsSemiLatticeMax S where
  singleton: ι -> S
  mem_singleton: ∀i, i ∈ singleton i
  remove [DecidableEq ι]: ι -> S -> S
  mem_remove [DecidableEq ι]:  ∀(s: S) (x i: ι), x ∈ s -> i ≠ x -> x ∈ remove i s
  le_spec {a b: S}: a ≤ b ↔ a ⊆ b

instance : FiniteSupportOps (LazyFinset ι) ι where
  all s f := ∀x ∈ s, f x
  all_spec s f := by simp

instance : FiniteSupport (LazyFinset ι) ι where
  singleton := ({·})
  mem_singleton _ := LazyFinset.mem_singleton.mpr rfl
  remove := LazyFinset.erase
  mem_remove := by
    intro _ s x i hx ne
    apply LazyFinset.mem_erase.mpr
    apply And.intro hx
    symm; assumption
  le_spec := Iff.rfl

instance : FiniteSupportOps Nat Nat where
  all n f := ∀x < n, f x
  all_spec n f := by
    simp [Nat.mem_toLazyFinset, Nat.mem_iff_lt]

instance : FiniteSupport Nat Nat where
  singleton := (· + 1)
  mem_singleton _ := by rw [Nat.mem_iff_lt]; apply Nat.lt_succ_self
  remove i s := if i + 1 = s then i else s
  mem_remove := by
    intro _ s x i hx ne
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

end

namespace FiniteSupport

variable [FiniteSupport S ι]

def coe_max_sub_max_coe (a b: S) : (a ⊔ b: LazyFinset ι) ≤ ((a ⊔ b: S): LazyFinset ι) := by
  apply max_le
  rw [FiniteSupport.le_spec]
  rw [LazyFinset.coe_sub]
  simp [←FiniteSupport.le_spec]
  apply le_max_left
  rw [FiniteSupport.le_spec]
  rw [LazyFinset.coe_sub]
  simp [←FiniteSupport.le_spec]
  apply le_max_right

def mem_max (i: ι) (a b: S) : i ∈ a -> i ∈ a ⊔ b := by
  classical
  intro h
  apply coe_max_sub_max_coe
  apply LazyFinset.mem_append.mpr
  left; assumption

end FiniteSupport
