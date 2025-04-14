import Math.Algebra.Ring.Char
import Math.Algebra.Ring.Basic
import Math.Algebra.Ring.Impls.Fin
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
variable {n}

end ZMod
