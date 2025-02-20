import Math.Algebra.Ring.Theory.Basic
import Math.Data.Set.Basic
import Math.Order.Lattice.Complete
import Math.Order.GaloisConnection
import Math.Data.Set.Lattice
import Math.Algebra.Group.Units.Defs

namespace Ring

structure AddSubgroup (R: Ring α) where
  carrier: Set R
  mem_zero: 0 ∈ carrier
  mem_add: ∀{x y}, x ∈ carrier -> y ∈ carrier -> x + y ∈ carrier
  mem_neg: ∀{x}, x ∈ carrier -> -x ∈ carrier

structure Subring (R: Ring α) extends AddSubgroup R where
  mem_one: 1 ∈ carrier
  mem_mul: ∀{x y}, x ∈ carrier -> y ∈ carrier -> x * y ∈ carrier

def Subring.Elem (s: Subring R) : Type _ := s.carrier

attribute [coe] Subring.Elem

instance : CoeSort (Subring R) (Type _) where
  coe := Subring.Elem

def AddSubgroup.carrier_inj {a b: AddSubgroup R} : a.carrier = b.carrier ↔ a = b :=
  Function.Injective.eq_iff <| by
    intro a b eq
    cases a; congr

def Subring.carrier_inj {a b: Subring R} : a.carrier = b.carrier ↔ a = b :=
  Function.Injective.eq_iff (f₀ := fun x: Subring R => x.carrier) <| by
    intro a b eq
    cases a; congr
    apply AddSubgroup.carrier_inj.mp
    assumption

instance (R: Ring α) : Membership R (AddSubgroup R) where
  mem i x := x ∈ i.carrier

instance (R: Ring α) : Membership R (Subring R) where
  mem i x := x ∈ i.carrier

@[ext]
def AddSubgroup.ext {a b: AddSubgroup R} : (∀x, x ∈ a ↔ x ∈ b) -> a = b := by
  intro h
  apply AddSubgroup.carrier_inj.mp
  ext; apply h

@[ext]
def Subring.ext {a b: Subring R} : (∀x, x ∈ a ↔ x ∈ b) -> a = b := by
  intro h
  apply Subring.carrier_inj.mp
  ext; apply h

namespace Subring

variable (S: Subring R)

def mem_sub {a b: R} : a ∈ S -> b ∈ S -> a - b ∈ S := by
  intro _ _
  rw [sub_eq_add_neg]
  apply S.mem_add
  assumption
  apply S.mem_neg
  assumption

def mem_nsmul {n: ℕ} {a: R} : a ∈ S -> n • a ∈ S := by
  intro _
  induction n with
  | zero => rw [zero_nsmul]; apply S.mem_zero
  | succ n ih => rw [succ_nsmul]; apply S.mem_add <;> assumption

def mem_zsmul {n: ℤ} {a: R} : a ∈ S -> n • a ∈ S := by
  intro _
  cases n using Int.coe_cases with
  | ofNat => rw [zsmul_ofNat]; apply S.mem_nsmul; assumption
  | negSucc n => rw [zsmul_negSucc]; apply S.mem_neg; apply S.mem_nsmul; assumption

def mem_npow {n: ℕ} {a: R} : a ∈ S -> a ^ n ∈ S := by
  intro _
  induction n with
  | zero => rw [npow_zero]; apply S.mem_one
  | succ n ih => rw [npow_succ]; apply S.mem_mul <;> assumption

def mem_natCast {n: ℕ} : (n: R) ∈ S := by
  rw [natCast_eq_nsmul_one]
  apply mem_nsmul
  apply S.mem_one

def mem_intCast {n: ℤ} : (n: R) ∈ S := by
  rw [intCast_eq_zsmul_one]
  apply mem_zsmul
  apply S.mem_one

def mem_ofNat {n: ℕ} : (OfNat.ofNat (n+2): R) ∈ S := by
  rw [ofNat_eq_natCast]
  apply mem_natCast

instance : Zero S where
  zero := ⟨0, S.mem_zero⟩
instance : One S where
  one := ⟨1, S.mem_one⟩
instance : Add S where
  add a b := ⟨a.val + b.val, S.mem_add a.property b.property⟩
instance : Mul S where
  mul a b := ⟨a.val * b.val, S.mem_mul a.property b.property⟩
instance : Neg S where
  neg a := ⟨-a.val, S.mem_neg a.property⟩

instance : Sub S where
  sub a b := ⟨a.val - b.val, S.mem_sub a.property b.property⟩

instance : SMul ℕ S where
  smul n a := ⟨n • a.val, S.mem_nsmul a.property⟩
instance : SMul ℤ S where
  smul n a := ⟨n • a.val, S.mem_zsmul a.property⟩
instance : Pow S ℕ where
  pow a n := ⟨a.val ^ n, S.mem_npow a.property⟩

instance : NatCast S where
  natCast n := ⟨n, S.mem_natCast⟩
instance : IntCast S where
  intCast n := ⟨n, S.mem_intCast⟩
instance : OfNat S (n + 2) where
  ofNat := ⟨OfNat.ofNat (n + 2), S.mem_ofNat⟩

instance : IsRing S where
  add_comm := by
    intros
    apply Subtype.val_inj
    apply add_comm
  add_assoc := by
    intros
    apply Subtype.val_inj
    apply add_assoc
  mul_assoc := by
    intros
    apply Subtype.val_inj
    apply mul_assoc
  zero_add := by
    intros
    apply Subtype.val_inj
    apply zero_add
  add_zero := by
    intros
    apply Subtype.val_inj
    apply add_zero
  one_mul := by
    intros
    apply Subtype.val_inj
    apply one_mul
  mul_one := by
    intros
    apply Subtype.val_inj
    apply mul_one
  zero_mul := by
    intros
    apply Subtype.val_inj
    apply zero_mul
  mul_zero := by
    intros
    apply Subtype.val_inj
    apply mul_zero
  left_distrib := by
    intros
    apply Subtype.val_inj
    apply mul_add
  right_distrib := by
    intros
    apply Subtype.val_inj
    apply add_mul
  zero_nsmul := by
    intros
    apply Subtype.val_inj
    apply zero_nsmul
  succ_nsmul := by
    intros
    apply Subtype.val_inj
    apply succ_nsmul
  npow_zero := by
    intros
    apply Subtype.val_inj
    apply npow_zero
  npow_succ := by
    intros
    apply Subtype.val_inj
    apply npow_succ
  zsmul_ofNat := by
    intros
    apply Subtype.val_inj
    apply zsmul_ofNat
  zsmul_negSucc := by
    intros
    apply Subtype.val_inj
    apply zsmul_negSucc
  neg_add_cancel := by
    intros
    apply Subtype.val_inj
    apply neg_add_cancel
  intCast_ofNat := by
    intros
    apply Subtype.val_inj
    apply intCast_ofNat
  intCast_negSucc := by
    intros
    apply Subtype.val_inj
    apply intCast_negSucc
  natCast_zero := by
    intros
    apply Subtype.val_inj
    apply natCast_zero
  natCast_succ := by
    intros
    apply Subtype.val_inj
    apply natCast_succ
  ofNat_eq_natCast := by
    intros
    apply Subtype.val_inj
    apply ofNat_eq_natCast
  sub_eq_add_neg := by
    intros
    apply Subtype.val_inj
    apply sub_eq_add_neg

end Subring

def AddSubgroup.setoid {R: Ring α} (i: AddSubgroup R) : Setoid R where
  r a b := a - b ∈ i
  iseqv := {
    refl x := by
      rw [sub_self]
      apply i.mem_zero
    symm := by
      intro x y h
      rw [←neg_sub]
      apply i.mem_neg
      assumption
    trans := by
      intro x y z hx hy
      rw [←add_zero (_ - _), ←sub_self y,
        sub_add_assoc, ←add_sub_assoc, add_comm, sub_eq_add_neg, add_assoc (_ + _),
          add_comm _ y, add_comm _ x, ←sub_eq_add_neg, ←sub_eq_add_neg]
      apply i.mem_add
      assumption
      assumption
  }

-- every ring homomorphism identifies a subring of R
def Subring.ofHom {R S: Ring α} (f: S →+* R) : Subring R where
  carrier := Set.range f
  mem_zero := by
    exists 0
    rw [resp_zero]
  mem_one := by
    exists 1
    rw [resp_one]
  mem_add := by
    rintro _ _ ⟨_, rfl⟩ ⟨_, rfl⟩
    rw [←resp_add]
    apply Set.mem_range'
  mem_neg := by
    rintro _ ⟨_, rfl⟩
    rw [←resp_neg]
    apply Set.mem_range'
  mem_mul := by
    rintro _ _ ⟨_, rfl⟩ ⟨_, rfl⟩
    rw [←resp_mul]
    apply Set.mem_range'

end Ring
