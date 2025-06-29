import Math.Algebra.Ring.Theory.Basic
import Math.Data.Set.Basic
import Math.Order.Lattice.Complete
import Math.Order.GaloisConnection
import Math.Data.Set.Lattice
import Math.Algebra.Group.Units.Defs
import Math.Algebra.Ring.SetLike.Basic

def AddSubgroup.setoid {R: Ring α} (i: AddSubgroup R) : Setoid R where
  r a b := a - b ∈ i
  iseqv := {
    refl x := by
      rw [sub_self]
      apply mem_zero
    symm := by
      intro x y h
      rw [←neg_sub]
      apply mem_neg
      assumption
    trans := by
      intro x y z hx hy
      rw [←add_zero (_ - _), ←sub_self y,
        sub_add_assoc, ←add_sub_assoc, add_comm, sub_eq_add_neg, add_assoc (_ + _),
          add_comm _ y, add_comm _ x, ←sub_eq_add_neg, ←sub_eq_add_neg]
      apply mem_add
      assumption
      assumption
  }

namespace Subring

-- there is a homomorphism between to a subring from each of it's subsets
def Hom [RingOps R] (s t: Subring R) (h: s ⊆ t) : s ↪+* t where
  toFun x := ⟨x.val, h _ x.property⟩
  inj' := by
    intro a b eq
    cases a; cases eq; rfl
  map_zero := rfl
  map_one := rfl
  map_add := rfl
  map_mul := rfl

def bij_range [RingOps R] [RingOps S] [IsRing R] [IsRing S] (f: S ↪+* R) : S ⇔+* range f where
  toBijection := Bijection.range f.toEmbedding
  map_zero := by
    apply Subtype.val_inj
    apply map_zero f
  map_one := by
    apply Subtype.val_inj
    apply map_one f
  map_add {x y} := by
    apply Subtype.val_inj
    apply map_add f
  map_mul {x y} := by
    apply Subtype.val_inj
    apply map_mul f

noncomputable def equiv_range [RingOps R] [RingOps S] [IsRing R] [IsRing S] (f: S ↪+* R) : S ≃+* range f := {
  (bij_range f).toEquiv, bij_range f with
}

end Subring
