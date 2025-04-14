import Math.Algebra.Ring.Char
import Math.Algebra.Ring.Basic
import Math.Algebra.Algebra.Hom
import Math.Algebra.Ring.Units.Defs
import Math.Algebra.Field.Impls.Fin
import Math.Order.OrderIso
import Math.Algebra.AddGroupWithOne.Hom

def ZMod : ℕ -> Type
| 0 => ℤ
| n + 1 => Fin (n + 1)

namespace ZMod

macro "infer_zmod_instnace" n:ident x:term : term => `(match ($n) with
  | 0 => inferInstanceAs ($x ℤ)
  | _ + 1 => inferInstanceAs ($x (Fin _)))

instance : RingOps (ZMod n) := infer_zmod_instnace n RingOps
instance : IsRing (ZMod n) := infer_zmod_instnace n IsRing
instance : IsCommMagma (ZMod n) := infer_zmod_instnace n IsCommMagma

def equivInt : ZMod 0 ≃+* Int := RingEquiv.refl
def equivFin (n: ℕ) : ZMod (n + 1) ≃+* Fin (n + 1) := RingEquiv.refl

instance : HasChar (ZMod n) n :=
  match n with
  | 0 => inferInstanceAs (HasChar ℤ 0)
  | n + 1 => inferInstanceAs (HasChar (Fin (n + 1)) (n + 1))

def n_eq_zero : (n: ZMod n) = 0 := HasChar.natCast_eq_zero
def n_nsmul_eq_zero (x: ZMod n) : n • x = 0 := by rw [nsmul_eq_natCast_mul, n_eq_zero, zero_mul]

def natCast_mod_n (a: ℕ) : ((a % n): ZMod n) = a := by
  conv => { rhs; rw [←Nat.div_add_mod a n] }
  rw [natCast_add, natCast_mul]
  simp [n_eq_zero]

def intCast_mod_n (a: ℤ) : ((a % (n: ℤ)): ZMod n) = a := by
  conv => { rhs; rw [←Int.ediv_add_emod a n] }
  rw [←intCast_add, ←intCast_mul]
  simp [intCast_ofNat, n_eq_zero]

def toInt : ∀{n}, ZMod n ↪ ℤ
| 0 => Embedding.rfl
| _ + 1 => Embedding.trans Fin.embedNat ⟨Int.ofNat, by apply Int.ofNat.inj⟩

instance : LE (ZMod n) := infer_zmod_instnace n LE
instance : LT (ZMod n) := infer_zmod_instnace n LT

instance : Min (ZMod n) := infer_zmod_instnace n Min
instance : Max (ZMod n) := infer_zmod_instnace n Max

instance : IsDecidableLinearOrder (ZMod n) := infer_zmod_instnace n IsDecidableLinearOrder
-- this decidable eq inst is faster than from `IsDecidableLinearOrder`
instance : DecidableEq (ZMod n) := infer_zmod_instnace n DecidableEq

instance : Repr (ZMod n) := infer_zmod_instnace n Repr

instance : Subsingleton (ZMod 1) := inferInstanceAs (Subsingleton (Fin 1))
instance [h: Nat.NeOne n] : IsNontrivial (ZMod n) := match n, h with
  | 0, _ => inferInstanceAs (IsNontrivial ℤ)
  | n + 2, _ => ⟨0, 1, by
    show Fin.mk 0 _ ≠ Fin.mk 1 _
    intro h
    have := Fin.mk.inj h
    contradiction⟩

instance : Inhabited (ZMod n) := ⟨0⟩

instance [h: Fact (Nat.IsPrime n)] : FieldOps (ZMod n) := match n, h with
  | 0, _ => by
    have : Nat.IsPrime 0 := Fact.proof
    contradiction
  | n + 1, h => inferInstanceAs (FieldOps (Fin _))
instance [h: Fact (Nat.IsPrime n)] : IsField (ZMod n) := match n, h with
  | 0, _ => by
    have : Nat.IsPrime 0 := Fact.proof
    contradiction
  | n + 1, h => inferInstanceAs (IsField (Fin _))

private def preToUnit {n: ℕ} (x: ZMod n) (coprime: Int.gcd x.toInt n = 1 := by decide) : Units (ZMod n) := match n with
| 0 => if x < 0 then -1 else 1
| _ + 1 => Fin.toUnit x coprime

private def preToUnit_val (x: ZMod n) (coprime: Int.gcd x.toInt n = 1) : (preToUnit x coprime).val = x := by
  cases n <;> unfold preToUnit <;> dsimp
  rw [Int.gcd, natCast_zero, Int.natAbs_zero, Nat.gcd_zero_right, Int.natAbs_eq_iff] at coprime
  replace coprime : x = 1 ∨ x = -1 := coprime
  apply toInt.inj
  rcases coprime with rfl | rfl
  · rw [if_neg]
    rfl
    decide
  · rw [if_pos]
    rfl
    decide
  · rfl

-- the units of ZMOD n are precisely the the values which are coprime with n
def toUnit : { x: ZMod n // Int.gcd x.toInt n = 1 } ≃ Units (ZMod n) where
  toFun x := preToUnit x.val x.property
  invFun x := ⟨x.val, by
    cases n <;> (unfold toInt; dsimp)
    · show Int.gcd x.val 0 = 1
      rcases le_total 0 x.val with h | h
      rw [Int.eq_one_of_mul_eq_one_left h x.inv_mul_val]
      rfl
      have := x.inv_mul_val
      rw [←neg_neg (x.inv * x.val), neg_mul_left, neg_mul_right] at this
      rw [←neg_neg x.val]
      rw [Int.eq_one_of_mul_eq_one_left _ this]
      rfl
      rwa [←Int.neg_le_neg_iff, neg_neg]
    · rename_i n
      unfold Int.gcd
      rw [Int.natAbs_ofNat]
      simp
      show x.val.val.gcd (n + 1) = 1
      cases n
      have : x.val = 0 := Subsingleton.allEq _ _
      rw [this]; rfl
      rename_i n
      apply flip Nat.dvd_antisymm
      apply Nat.one_dvd
      have : (x.val * x.inv).val = 1 := by rw [x.val_mul_inv]; rfl
      conv => { rhs; rw [←this] }
      show _ ∣ (_ * _) % _
      apply (Nat.dvd_mod_iff _).mpr
      apply Nat.dvd_trans
      apply Nat.gcd_dvd_left
      apply Nat.dvd_mul_right
      apply Nat.gcd_dvd_right⟩
  leftInv x := by simp [ZMod.preToUnit_val x.val x.property]
  rightInv x := by
    apply Units.val_inj.mp
    simp [ZMod.preToUnit_val]

@[simp] def apply_toUnit_val (x: { x: ZMod n // Int.gcd x.toInt n = 1 }) : (toUnit x).val = x.val := preToUnit_val _ _
@[simp] def apply_symm_toUnit (x: Units (ZMod n)) : (toUnit.symm x).val = x.val := rfl

def ofInt (n: ℕ) : ℤ →ₐ[ℤ] ZMod n := {
    toFun x := x
    map_add {x y} := by rw [intCast_add]
    map_mul {x y} := by rw [intCast_mul]
    map_algebraMap x := rfl
  }

def apply_ofInt (n: ℕ) (x: ℤ) : ofInt n x = x := rfl

def toInt_ofInt (x: ℤ) : toInt (ofInt n x) = x % n := by
  cases n
  erw [Int.emod_zero]; rfl
  rename_i n
  show Fin.val _ = x % (n + 1)
  rw [apply_ofInt, ←Int.ofNat_succ]
  show Fin.val ⟨Int.toNat _, _⟩ = x % (n + 1)
  simp
  rw [max_eq_left.mpr]
  apply Int.emod_nonneg
  omega
def ofInt_toInt (x: ZMod n) : ofInt n (toInt x) = x := by
  cases n
  rfl
  rename_i n
  rw [apply_ofInt]
  erw [intCast_ofNat]
  show ⟨x.val % (n + 1: ℕ), _⟩ = x
  congr
  rw [Nat.mod_eq_of_lt x.isLt]

@[induction_eliminator]
def induction {n: ℕ} {motive: ZMod n -> Prop} (ofInt: ∀x: ℤ, motive (ZMod.ofInt n x)) : ∀x, motive x := by
  intro x
  rw [←ofInt_toInt x]
  apply ofInt

private def liftHelper {n: ℕ} {A: Type*} [AddGroupOps A] [IsAddGroup A] (f: {f: ℤ →+ A // f n = 0}) : ∀x, n • f.val x = 0 := by
    suffices ∀x: ℕ, n • f.val x = 0 by
      intro x
      cases x with
      | ofNat x => apply this
      | negSucc x =>
        rw [Int.negSucc_eq, map_neg, ←zsmul_ofNat, zsmul_neg,
          ←Int.ofNat_succ, zsmul_ofNat, this, neg_zero]
    intro x
    rw [←map_nsmul]
    show f.val ((n * x: ℕ)) = 0
    induction x with
    | zero => rw [mul_zero, natCast_zero, map_zero]
    | succ x ih => rw [Nat.mul_succ, natCast_add, map_add, ih, f.property, add_zero]

section

variable {A: Type*} [AddGroupOps A] [IsAddGroup A]

def lift (n: ℕ) : { f: ℤ →+ A // f n = 0 } ≃ (ZMod n →+ A) :=
  match n with
  | 0 => {
    toFun f := f.1
    invFun f := ⟨f, map_zero f⟩
    leftInv _ := rfl
    rightInv _ := rfl
  }
  | n + 1 => {
    toFun f := {
      toFun x := f.val x.toInt
      map_zero := map_zero f.val
      map_add {x y} := by
        show f.val ((x.val + y.val) % (n + 1): ℕ) = _
        rw [←map_add f.val]
        show _ = f.val (x.val + y.val)
        rw [←natCast_add]
        rw (occs := [2]) [←Nat.div_add_mod (x.val + y.val) (n + 1)]
        rw (occs := [3]) [natCast_add]
        rw [natCast_mul, map_add, ←smul_eq_mul, zsmul_ofNat, map_nsmul]
        rw [liftHelper, zero_add]
    }
    invFun f := {
      val := f.comp (toAddGroupHom (ofInt _))
      property := by
        show f (ofInt _ _) = 0
        rw [map_natCast, n_eq_zero, map_zero]
    }
    leftInv f := by
      ext x
      simp
      show f.val (toInt (ofInt _ x)) = f.val x
      rw [toInt_ofInt, ←zero_add (f.val _)]
      rw (occs := [1]) [←liftHelper f (x / (n + 1: ℕ))]
      rw [←map_nsmul, ←map_add, ←zsmul_ofNat,
        smul_eq_mul, Int.ediv_add_emod]
    rightInv f := by
      ext x
      simp
      show f (ofInt _ (toInt x)) = f x
      rw [ofInt_toInt]
  }

def apply_lift (n: ℕ) (f: { f: ℤ →+ A // f n = 0 }) (x: ZMod n) : lift n f x = f.val (toInt x) := by
  cases n <;> rfl

def symm_apply_lift (n: ℕ) (f: ZMod n →+ A) (x: ℤ) : ((lift n).symm f).val x = f (ofInt n x) := by
  cases n <;> rfl

def lift_ofInt (n: ℕ) (f: { f: ℤ →+ A // f n = 0 }) : lift n f (ofInt n x) = f.val x := by
  cases n
  rfl
  rename_i n
  have : ((lift (n + 1)).invFun ((lift (n + 1)).toFun f)).val = (f.val: _ -> _) := by rw [(lift (n + 1) (A := A)).leftInv f]
  apply congrFun this

def symm_lift_toInt (n: ℕ) (f: ZMod n →+ A) (x: ZMod n) : ((lift n).symm f).val (toInt x) = f x := by
  cases n
  rfl
  rename_i n
  have : (lift (n + 1)).toFun ((lift (n + 1)).invFun f) = (f: _ -> _) := by rw [(lift (n + 1) (A := A)).rightInv f]
  apply congrFun this

end

section

variable {A: Type*} [RingOps A] [IsRing A]

def liftRing (n: ℕ) : { f: ℤ →+* A // f n = 0 } ≃ (ZMod n →+* A) := {
  toFun f := {
    lift n ⟨f.val.toAddGroupHom, f.property⟩ with
    map_one := by
      show lift _ _ _ = _
      rw [←map_one (ofInt _), lift_ofInt]
      apply map_one f.val
    map_mul {x y} := by
      show lift _ _ _ = lift _ _ _ * lift _ _ _
      simp
      induction x with | ofInt x =>
      induction y with | ofInt y =>
      rw [←map_mul, lift_ofInt, lift_ofInt, lift_ofInt]
      apply map_mul f.val
  }
  invFun f := {
    val := f.comp (toRingHom (ofInt _))
    property := by
      show f (ofInt _ _) = 0
      rw [map_natCast, n_eq_zero, map_zero]
  }
  leftInv f := by
    ext x
    show lift n _ (ofInt n _) = _
    apply lift_ofInt
  rightInv f := by
    ext x
    induction x with | ofInt x =>
    erw [lift_ofInt]
    rfl
}

def apply_liftRing (n: ℕ) (f: { f: ℤ →+* A // f n = 0 }) (x: ZMod n) : liftRing n f x = f.val (toInt x) := by
  cases n <;> rfl

def symm_apply_liftRing (n: ℕ) (f: ZMod n →+* A) (x: ℤ) : ((liftRing n).symm f).val x = f (ofInt n x) := by
  cases n <;> rfl

def liftRing_ofInt (n: ℕ) (f: { f: ℤ →+* A // f n = 0 }) : liftRing n f (ofInt n x) = f.val x := by
  cases n
  rfl
  rename_i n
  have : ((liftRing (n + 1)).invFun ((liftRing (n + 1)).toFun f)).val = (f.val: _ -> _) := by rw [(liftRing (n + 1) (A := A)).leftInv f]
  apply congrFun this

def symm_liftRing_toInt (n: ℕ) (f: ZMod n →+* A) (x: ZMod n) : ((liftRing n).symm f).val (toInt x) = f x := by
  cases n
  rfl
  rename_i n
  have : (liftRing (n + 1)).toFun ((liftRing (n + 1)).invFun f) = (f: _ -> _) := by rw [(liftRing (n + 1) (A := A)).rightInv f]
  apply congrFun this

end

end ZMod
