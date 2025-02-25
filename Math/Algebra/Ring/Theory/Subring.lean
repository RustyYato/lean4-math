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

-- every ring homomorphism identifies a subring of R
def Subring.ofHom [RingOps R] [RingOps S] [IsRing R] [IsRing S] (f: S →+* R) : Subring R where
  carrier := Set.range f
  mem_zero' := by
    exists 0
    rw [resp_zero]
  mem_one' := by
    exists 1
    rw [resp_one]
  mem_add' := by
    rintro _ _ ⟨_, rfl⟩ ⟨_, rfl⟩
    rw [←resp_add]
    apply Set.mem_range'
  mem_neg' := by
    rintro _ ⟨_, rfl⟩
    rw [←resp_neg]
    apply Set.mem_range'
  mem_mul' := by
    rintro _ _ ⟨_, rfl⟩ ⟨_, rfl⟩
    rw [←resp_mul]
    apply Set.mem_range'

-- there is a homomorphism between to a subring from each of it's subsets
def Subring.Hom [RingOps R] (s t: Subring R) (h: s ⊆ t) : s ↪+* t where
  toFun x := ⟨x.val, h _ x.property⟩
  inj' := by
    intro a b eq
    cases a; cases eq; rfl
  resp_zero := rfl
  resp_one := rfl
  resp_add := rfl
  resp_mul := rfl
