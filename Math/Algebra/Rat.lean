import Math.Algebra.Ring
import Math.Data.Rat.Basic

local notation "⟦" f "⟧" => QuotLike.mk (Q := ℚ) f

instance : NatCast ℚ where
  natCast n := Rat.ofNat n

instance : IntCast ℚ where
  intCast n := Rat.mk (Fract.mk n 1) (Nat.gcd_one_right _)

instance : SMul ℕ ℚ where
  smul n q := (n: ℚ) * q

instance : SMul ℤ ℚ where
  smul n q := (n: ℚ) * q

instance : CheckedIntPow ℚ (· ≠ 0) where
  checked_pow x n _ := x ^ n

def Rat.natCast_succ (a: Nat) : ((a + 1: ℕ): ℚ) = (a + 1: ℚ) := by
  apply Rat.toFract.inj
  apply Fract.isReduced.spec
  apply Rat.isReduced
  apply Rat.isReduced
  apply Fract.trans _ (quot.exact' (Q := ℚ)).symm
  have : unwrapQuot (Q := ℚ) 1 = 1 := rfl
  rw [this]; clear this
  show _ = _
  show ((a + 1): Int) * 1 = (Fract.add _ _).num * 1
  rw [Int.mul_one, Int.mul_one]
  unfold Fract.add
  show _ = (a: Int) * 1 + 1
  rw [Int.mul_one]

def Rat.natCast_add (a b: Nat) : ((a + b: ℕ): ℚ) = (a + b: ℚ) := by
  induction b with
  | zero => erw [Nat.add_zero, add_zero]
  | succ b ih =>
    show (((a + b) + 1: Nat): ℚ) = _
    rw [natCast_succ, natCast_succ, ih, add_assoc]

instance : IsField ℚ where
  add_comm := Rat.add_comm
  mul_comm := Rat.mul_comm
  add_assoc := Rat.add_assoc
  mul_assoc := Rat.mul_assoc
  zero_add := Rat.zero_add
  add_zero := Rat.add_zero
  zero_mul := Rat.zero_mul
  mul_zero := Rat.mul_zero
  one_mul := Rat.one_mul
  mul_one := Rat.mul_one
  ofNat_eq_natCast _ := rfl
  natCast_zero := rfl
  natCast_succ := Rat.natCast_succ
  left_distrib _ _ _ := Rat.mul_add _ _ _
  right_distrib _ _ _ := Rat.add_mul _ _ _
  sub_eq_add_neg := Rat.sub_eq_add_neg
  zsmul_ofNat _ _ := rfl
  zsmul_negSucc := by
    intro n a
    show (-(Int.ofNat n.succ): ℚ) * _ = _
    rw [←Rat.neg_mul_left]
    rfl
  neg_add_cancel := Rat.neg_self_add
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl
  zero_nsmul := Rat.zero_mul
  succ_nsmul := by
    intro n a
    show _ * _ = _ + _
    erw [Rat.natCast_add, Rat.add_mul, Rat.one_mul]
    rfl
  npow_zero _ := rfl
  npow_succ := by
    intro n a
    quot_ind a
    rw [Rat.mk_npow, Rat.mk_npow, Rat.mk_mul]
    apply quot.sound
    rfl
  mul_inv?_cancel := Rat.mul_inv_self
  div?_eq_mul_inv? _ _ _ := rfl
  zpow?_ofNat _ _ := rfl
  zpow?_negSucc a b h := by
    show Rat.zpow _ _ = Rat.npow _ _
    unfold Rat.zpow
    dsimp
    rw [dif_neg h]
    rfl
  zero_ne_one := by decide

instance : IsNontrivial ℚ where
  zero_ne_one := by
    intro h
    contradiction

def Rat.char_eq : char Rat = 0 := by
  apply char_eq_of_natCast_eq_zero
  rfl
  intro m h
  cases h
  apply Nat.dvd_refl
