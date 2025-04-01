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

-- every ring homomorphism identifies a subring of R
def range
  [RingOps R] [RingOps S] [IsRing R] [IsRing S]
  [FunLike F S R] [IsZeroHom F S R] [IsOneHom F S R] [IsAddHom F S R] [IsMulHom F S R]
  (f: F) : Subring R where
  carrier := Set.range f
  mem_zero := by
    exists 0
    rw [map_zero]
  mem_one := by
    exists 1
    rw [map_one]
  mem_add := by
    rintro _ _ ⟨_, rfl⟩ ⟨_, rfl⟩
    rw [←map_add]
    apply Set.mem_range'
  mem_neg := by
    rintro _ ⟨_, rfl⟩
    rw [←map_neg]
    apply Set.mem_range'
  mem_mul := by
    rintro _ _ ⟨_, rfl⟩ ⟨_, rfl⟩
    rw [←map_mul]
    apply Set.mem_range'

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

def embed_range [RingOps R] [RingOps S] [IsRing R] [IsRing S] (f: S ↪+* R) : S ↪+* range f where
  toFun s := ⟨f s, Set.mem_range'⟩
  inj' := by
    intro x y eq
    apply f.inj
    apply Subtype.mk.inj eq
  map_zero := by
    dsimp
    congr
    rw [map_zero]
  map_one := by
    dsimp
    congr
    rw [map_one]
  map_add {x y} := by
    dsimp
    congr
    rw [map_add]
  map_mul {x y} := by
    dsimp
    congr
    rw [map_mul]

noncomputable def equiv_range [RingOps R] [RingOps S] [IsRing R] [IsRing S] (f: S ↪+* R) : S ≃+* range f where
  toFun := embed_range f
  invFun x := Classical.choose x.property
  leftInv := by
    intro s
    dsimp
    apply f.inj
    have : f s ∈ range f := Set.mem_range'
    symm; apply Classical.choose_spec this
  rightInv := by
    intro ⟨r, hr⟩
    show Subtype.mk _ _ = _
    congr
    symm
    exact Classical.choose_spec hr
  map_zero := map_zero _
  map_one := map_one _
  map_add := map_add _
  map_mul := map_mul _

end Subring
