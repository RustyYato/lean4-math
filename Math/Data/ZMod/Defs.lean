import Math.Algebra.Ring.Char
import Math.Algebra.Ring.Basic
import Math.Algebra.Algebra.Hom
import Math.Algebra.Ring.Units.Defs
import Math.Algebra.Field.Impls.Fin
import Math.Algebra.Group.Impls.Prod
import Math.Order.OrderIso
import Math.Algebra.AddGroupWithOne.Hom
import Math.Type.Finite
import Math.Data.Int.Gcd

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

@[simp]
def toInt_zero : toInt (0: ZMod n) = 0 := by
  cases n <;> rfl

@[simp]
def toInt_eq_zero : toInt (x: ZMod n) = 0 -> x = 0 := by
  intro h
  cases n
  assumption
  rename_i n
  unfold toInt at h
  simp at h
  cases x; cases h
  rfl

def toInt_natAbs_lt_n (x: ZMod n) (h: n ≠ 0) : toInt x < n := by
  match n with
  | n + 1 =>
  apply Int.ofNat_lt.mpr
  apply Fin.isLt

def toInt_nonneg (x: ZMod n) (h: n ≠ 0) : 0 ≤ toInt x := by
  match n with
  | n + 1 =>
  apply Int.ofNat_le.mpr
  apply Nat.zero_le

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

instance [h: Nat.IsPrimeClass n] : FieldOps (ZMod n) := match n, h with
  | 0, _ => by contradiction
  | n + 1, h => inferInstanceAs (FieldOps (Fin _))
instance [h: Nat.IsPrimeClass n] : IsField (ZMod n) := match n, h with
  | 0, _ => by contradiction
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
      rw [←neg_neg (x.inv * x.val), ←neg_mul, ←mul_neg] at this
      rw [←neg_neg x.val]
      rw [Int.eq_one_of_mul_eq_one_left _ this]
      rfl
      rwa [←Int.neg_le_neg_iff, neg_neg]
    · rename_i n
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
  rw [apply_ofInt, ←natCast_succ]
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

def ofInt_n (n: ℕ) : ofInt n n = 0 := by
  show Int.cast (Nat.cast n) = 0
  rw [intCast_ofNat]
  apply n_eq_zero

def ofInt_emod (n: ℕ) (x: ℤ) : ofInt n x = ofInt n (x % n) := by
  rw [←zero_add (ofInt n (x % _)), ←zero_mul (ofInt n (x / n)), ←ofInt_n,
    ←map_mul (ofInt n), ←map_add, Int.ediv_add_emod]

@[induction_eliminator]
def induction {n: ℕ} {motive: ZMod n -> Prop} (ofInt: ∀x: ℤ, motive (ZMod.ofInt n x)) : ∀x, motive x := by
  intro x
  rw [←ofInt_toInt x]
  apply ofInt

def intCast_toInt (x: ZMod n) : (toInt x) = x := ofInt_toInt x
def toInt_intCast (x: ℤ) : toInt (x: ZMod n) = x % n := toInt_ofInt _

def toInt_neg (x: ZMod n) (hx: x ≠ 0) : toInt x + toInt (-x) = n := by
  induction x with | ofInt x =>
  rw [←map_neg, toInt_ofInt, toInt_ofInt,
    Int.neg_emod, if_neg]
  simp
  rw [←add_sub_assoc, add_comm, add_sub_cancel']
  rintro ⟨k, rfl⟩
  replace hx : Int.cast (n * k) ≠ (0: ZMod n) := hx
  rw [←intCast_mul, intCast_ofNat, n_eq_zero, zero_mul] at hx
  contradiction

def toInt_add (x y: ZMod n) : ∃k, toInt (x + y) = toInt x + toInt y - k ∧ (k = 0 ∨ k = n) := by
  cases n
  exists 0
  simp; rfl
  rename_i n
  if toInt (x + y) ≥ toInt x + toInt y then
    exists 0
    simp
    apply flip le_antisymm
    assumption
    apply Int.ofNat_le.mpr
    apply Nat.mod_le
  else
    rename_i h
    rw [Fin.add_def] at h
    simp at h
    replace h : (((x.val + y.val) % (n + 1): ℕ): ℤ) < (x.val: ℤ) + (y.val: ℤ) := h
    rw [←natCast_add] at h
    exists (n + 1: ℕ)
    apply And.intro _ (.inr rfl)
    rw [Fin.add_def]
    show (((x.val + y.val) % (n + 1): ℕ): ℤ) = (x.val: ℤ) + (y.val: ℤ) - _
    rw [←natCast_add]
    rw (occs := [2]) [←Nat.div_add_mod (x.val + y.val) (n + 1)]
    rw [natCast_add, sub_eq_add_neg, add_comm_right,
      ←sub_eq_add_neg]; rw [←mul_one (Nat.cast (n + 1)),
        natCast_mul, ←mul_sub]
    rw (occs := [1]) [←zero_add ( Nat.cast _)]; congr
    rw [←mul_zero]; congr
    suffices n + 1 ≤ x.val + y.val by
      rw [Nat.div_eq, if_pos, Nat.div_eq_of_lt]
      simp
      apply lt_of_lt_of_le
      apply Nat.sub_lt_sub_right
      assumption
      apply Nat.add_lt_add
      apply x.isLt
      apply y.isLt
      simp
      simp
      assumption
    apply Decidable.byContradiction
    intro g; simp at g
    rw [Nat.mod_eq_of_lt] at h
    exact lt_irrefl h
    assumption

private def liftHelper {n: ℕ} {A: Type*} [AddGroupOps A] [IsAddGroup A] (f: {f: ℤ →+ A // f n = 0}) : ∀x, n • f.val x = 0 := by
    suffices ∀x: ℕ, n • f.val x = 0 by
      intro x
      cases x with
      | ofNat x => apply this
      | negSucc x =>
        rw [Int.negSucc_eq, map_neg, ←zsmul_ofNat, zsmul_neg,
          ←natCast_succ, zsmul_ofNat, this, neg_zero]
    intro x
    rw [←map_nsmul]
    show f.val ((n * x: ℕ)) = 0
    induction x with
    | zero => rw [mul_zero, natCast_zero, map_zero]
    | succ x ih => rw [Nat.mul_succ, natCast_add, map_add, ih, f.property, add_zero]

section

variable {A: Type*} [AddGroupOps A] [IsAddGroup A] [GroupOps A] [IsGroup A]

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

def lift_exp (n: ℕ) : { f: ℤ →ₐ* A // f n = 1 } ≃ (ZMod n →ₐ* A) := by
  apply Equiv.congrEquiv _ _ (lift n (A := AddOfMul A))
  refine Equiv.congrSubtype ?_ ?_
  exact Equiv.exp_hom_equiv_addgroup_hom.symm
  rfl
  exact Equiv.exp_hom_equiv_addgroup_hom.symm

def apply_lift (n: ℕ) (f: { f: ℤ →+ A // f n = 0 }) (x: ZMod n) : lift n f x = f.val (toInt x) := by
  cases n <;> rfl

def apply_lift_exp (n: ℕ) (f: { f: ℤ →ₐ* A // f n = 1 }) (x: ZMod n) : lift_exp n f x = f.val (toInt x) := by
  cases n <;> rfl

def symm_apply_lift (n: ℕ) (f: ZMod n →+ A) (x: ℤ) : ((lift n).symm f).val x = f (ofInt n x) := by
  cases n <;> rfl

def symm_apply_lift_exp (n: ℕ) (f: ZMod n →ₐ* A) (x: ℤ) : ((lift_exp n).symm f).val x = f (ofInt n x) := by
  cases n <;> rfl

def lift_ofInt (n: ℕ) (f: { f: ℤ →+ A // f n = 0 }) : lift n f (ofInt n x) = f.val x := by
  cases n
  rfl
  rename_i n
  have : ((lift (n + 1)).invFun ((lift (n + 1)).toFun f)).val = (f.val: _ -> _) := by rw [(lift (n + 1) (A := A)).leftInv f]
  apply congrFun this

def lift_exp_ofInt (n: ℕ) (f: { f: ℤ →ₐ* A // f n = 1 }) : lift_exp n f (ofInt n x) = f.val x := by
  apply lift_ofInt (A := AddOfMul A)

def symm_lift_toInt (n: ℕ) (f: ZMod n →+ A) (x: ZMod n) : ((lift n).symm f).val (toInt x) = f x := by
  cases n
  rfl
  rename_i n
  have : (lift (n + 1)).toFun ((lift (n + 1)).invFun f) = (f: _ -> _) := by rw [(lift (n + 1) (A := A)).rightInv f]
  apply congrFun this

def symm_lift_exp_toInt (n: ℕ) (f: ZMod n →ₐ* A) (x: ZMod n) : ((lift_exp n).symm f).val (toInt x) = f x := by
  apply symm_lift_toInt (A := AddOfMul A)

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

instance [h: NeZero n] : Fintype (ZMod n) :=
  match n, h with
  | n + 1, _ => inferInstanceAs (Fintype (Fin (n + 1)))

instance [h: NeZero n] : IsFinite (ZMod n) := inferInstance

def not_finite : ¬IsFinite (ZMod 0) := by
  intro f
  apply Fintype.nat_not_Fintype
  apply @Fintype.ofIsFinite _ ?_
  apply IsFinite.ofEmbed (ZMod 0)
  refine ⟨Int.ofNat, fun {_ _} => Int.ofNat.inj⟩

@[simp]
def _root_.Fintype.card_zmod [h: NeZero n] : Fintype.card (ZMod n) = n :=
  match n, h with
  | _ + 1, _ => Fintype.card_fin _

macro_rules
| `(tactic|contradiction) => `(tactic|exfalso; apply not_finite; assumption)

-- given any equivalence between two ZMod, they must be the same type
def inj (h: ZMod n ≃ ZMod m) : n = m := by
  revert n m
  suffices ∀n m: ℕ, ZMod n ≃ ZMod m -> n < m -> False by
    intro n m h
    rcases Nat.lt_trichotomy n m with g | g | g
    have := this n m h
    contradiction
    assumption
    have := this m n h.symm
    contradiction
  intro n m h g
  match n with
  | 0 =>
    match m with
    | m + 1 =>
    clear g
    have : IsFinite (ZMod 0) := IsFinite.ofEquiv h
    contradiction
  | n + 1 =>
    match m with
    | m + 1 =>
    have := Fintype.card_eq_of_equiv h
    simp at this
    cases this
    exact lt_irrefl g

def toProd (n m: ℕ) : ZMod (n * m) →+ ZMod n × ZMod m := lift _ {
  val := {
    toFun x := (ZMod.ofInt n x, ZMod.ofInt m x)
    map_zero := by simp [map_zero]; rfl
    map_add {x y} := by simp [map_add]; rfl
  }
  property := by
    simp
    show (ofInt n (n * m), ofInt m (n * m)) = 0
    rw [ofInt_emod, Int.mul_emod_right, map_zero,
      ofInt_emod, Int.mul_emod_left, map_zero]; rfl
}

def apply_toProd (n m: ℕ) (x: ZMod (n * m)) : toProd n m x = (ZMod.ofInt n x.toInt, ZMod.ofInt m x.toInt) :=
  apply_lift _ _ _

def equiv_prod (n m: ℕ) (h: Nat.gcd n m = 1) : ZMod (n * m) ≃+ ZMod n × ZMod m := {
  toProd n m with
  invFun x := ZMod.ofInt _ (Int.chinese_remainder x.fst.toInt x.snd.toInt n m)
  leftInv x := by
    simp
    let p := (toProd n m x)
    let c := Int.chinese_remainder (toInt (toProd n m x).fst) (toInt (toProd n m x).snd) ↑n ↑m
    show ofInt (n * m) c = x
    have := Int.chinese_remainder_unique c (toInt x) n m h ?_ ?_
    rw [ofInt_emod, natCast_mul, this, ←natCast_mul, ←ofInt_emod, ofInt_toInt]
    rw [Int.chinese_remainder_mod_left, apply_toProd, toInt_ofInt, Int.emod_emod]
    assumption
    rw [Int.chinese_remainder_mod_right, apply_toProd, toInt_ofInt, Int.emod_emod]
    assumption
  rightInv x := by
    simp
    rw [apply_toProd]
    rw [toInt_ofInt]
    let c := (toInt x.fst).chinese_remainder (toInt x.snd) ↑n ↑m
    rw [ofInt_emod, ofInt_emod m,
      Int.emod_emod_of_dvd,
      Int.emod_emod_of_dvd,
      Int.chinese_remainder_mod_left,
      Int.chinese_remainder_mod_right,
      ←ofInt_emod, ←ofInt_emod m,
      ofInt_toInt, ofInt_toInt]
    assumption
    assumption
    rw [natCast_mul]; apply Int.dvd_mul_left
    rw [natCast_mul]; apply Int.dvd_mul_right
}

instance : NoZeroDivisors (ZMod 0) :=
  inferInstanceAs (NoZeroDivisors ℤ)

end ZMod
