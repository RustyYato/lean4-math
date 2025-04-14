import Math.Algebra.Ring.Char
import Math.Algebra.Ring.Basic
import Math.Algebra.Ring.Units.Defs
import Math.Algebra.Field.Impls.Fin
import Math.Order.OrderIso

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

end ZMod
