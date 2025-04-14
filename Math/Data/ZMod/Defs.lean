import Math.Algebra.Ring.Char
import Math.Algebra.Ring.Basic
import Math.Algebra.Ring.Impls.Fin
import Math.Order.OrderIso

def ZMod : ℕ -> Type
| 0 => ℤ
| n + 1 => Fin (n + 1)

namespace ZMod

instance : RingOps (ZMod n) :=
  match n with
  | 0 => inferInstanceAs (RingOps ℤ)
  | n + 1 => inferInstanceAs (RingOps (Fin (n + 1)))
instance : IsRing (ZMod n) :=
  match n with
  | 0 => inferInstanceAs (IsRing ℤ)
  | n + 1 => inferInstanceAs (IsRing (Fin (n + 1)))

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

instance : LE (ZMod n) where
  le a b := a.toInt ≤ b.toInt
instance : LT (ZMod n) where
  lt a b := a.toInt < b.toInt

instance : Min (ZMod n) where
  min :=
    match n with
    | 0 => min (α := ℤ)
    | _ + 1 => min (α := Fin _)
instance : Max (ZMod n) where
  max :=
    match n with
    | 0 => max (α := ℤ)
    | _ + 1 => max (α := Fin _)

def toIntHom : ZMod n ↪⊓⊔ Int where
  toEmbedding := toInt
  map_le _ _ := Iff.rfl
  map_min a b :=
    match n with
    | 0 => rfl
    | n + 1 => by
      show Int.ofNat (min (α := Fin (n + 1)) a b).val = Int.ofNat a.val ⊓ Int.ofNat b.val
      simp [Nat.min_def, Int.min_def]
      split <;> rfl
  map_max a b :=
    match n with
    | 0 => rfl
    | n + 1 => by
      show Int.ofNat (max (α := Fin (n + 1)) a b).val = Int.ofNat a.val ⊔ Int.ofNat b.val
      simp [Nat.max_def, Int.max_def]
      split <;> rfl

instance : IsLawfulLT (ZMod n) where
  lt_iff_le_and_not_le := lt_iff_le_and_not_le (α := ℤ)

instance : IsDecidableLinearOrder (ZMod n) := _root_.instIsDecidableLinearOrder toIntHom

end ZMod
