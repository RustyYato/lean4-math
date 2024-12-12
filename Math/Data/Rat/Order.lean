import Math.Data.Rat.Basic
import Math.Data.StdInt.Order

def Fract.LE (a b: Fract) := a.num * b.den ≤ b.num * a.den
def Fract.LT (a b: Fract) := a.num * b.den < b.num * a.den

local notation "⟦" f "⟧" => QuotLike.mk (Q := ℚ) f

instance : LT Fract := ⟨Fract.LT⟩
instance : LE Fract := ⟨Fract.LE⟩

instance : LT ℚ := ⟨fun a b => a.LT b.toFract⟩
instance : LE ℚ := ⟨fun a b => a.LE b.toFract⟩

def Fract.LE.spec (a b c d: Fract) : a ≈ c -> b ≈ d -> a ≤ b -> c ≤ d := by
  intro ac bd ab
  replace ab : a.num * _ ≤ _ *_ := ab
  show c.num * _ ≤ _ * _
  apply Int.le_of_mul_le_mul_right (a := (a.den * b.den))
  rw [Int.mul_assoc, Int.mul_left_comm d.den]
  rw [Int.mul_assoc, Int.mul_comm a.den b.den, Int.mul_left_comm c.den]
  rw [←Int.mul_assoc, ←Int.mul_assoc d.num, ←ac, ←bd]
  rw [Int.mul_assoc, Int.mul_comm d.den b.den, Int.mul_left_comm c.den]
  rw [Int.mul_assoc, Int.mul_comm c.den a.den, Int.mul_left_comm d.den]
  rw [←Int.mul_assoc, ←Int.mul_assoc b.num, Int.mul_comm c.den]
  apply Int.mul_le_mul_of_nonneg_right
  assumption
  rw [Int.ofNat_mul_ofNat]
  apply Int.ofNat_zero_le
  rw [Int.ofNat_mul_ofNat]
  apply Int.ofNat_lt.mpr
  apply Nat.mul_pos
  exact a.den_pos
  exact b.den_pos

def Fract.LT.spec (a b c d: Fract) : a ≈ c -> b ≈ d -> a < b -> c < d := by
  intro ac bd ab
  apply lt_of_not_le (α := Int)
  intro h
  apply not_le_of_lt (α := Int) ab
  apply Fract.LE.spec d c b a
  symm; assumption
  symm; assumption
  assumption

def Rat.mk_le (a b: Fract) : (⟦a⟧ ≤ ⟦b⟧) ↔ a ≤ b := by
  apply Iff.intro
  apply Fract.LE.spec
  symm; apply Fract.reduce.spec
  symm; apply Fract.reduce.spec
  apply Fract.LE.spec
  apply Fract.reduce.spec
  apply Fract.reduce.spec

def Rat.mk_lt (a b: Fract) : (⟦a⟧ < ⟦b⟧) ↔ a < b := by
  apply Iff.intro
  apply Fract.LT.spec
  symm; apply Fract.reduce.spec
  symm; apply Fract.reduce.spec
  apply Fract.LT.spec
  apply Fract.reduce.spec
  apply Fract.reduce.spec

instance (a b: Fract) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.num * _ ≤ _ * _))
instance (a b: Fract) : Decidable (a < b) := inferInstanceAs (Decidable (a.num * _ < _ * _))

instance (a b: ℚ) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.toFract ≤ b.toFract))
instance (a b: ℚ) : Decidable (a < b) := inferInstanceAs (Decidable (a.toFract < b.toFract))

instance : Min Fract := minOfLe
instance : Max Fract := maxOfLe
instance : Min ℚ := minOfLe
instance : Max ℚ := maxOfLe

instance : IsLinearOrder ℚ where
  lt_iff_le_and_not_le := by
    intro a b
    apply lt_iff_le_and_not_le (α := Int)
  lt_or_le := by
    intro a b
    apply lt_or_le (α := Int)
  le_antisymm := by
    intro a b ab ba
    quot_ind (a b)
    rw [Rat.mk_le] at ab ba
    have := le_antisymm (α := Int) ab ba
    apply quot.sound
    assumption
  le_trans := by
    intro a b c
    intro ab bc
    replace ab : a.num * _ ≤ _ * _ := ab
    replace bc : b.num * _ ≤ _ * _ := bc
    show a.num * _ ≤ _ * _
    replace ab := Int.mul_le_mul_of_nonneg_right (c := c.den) ab (Int.ofNat_zero_le _)
    replace bc := Int.mul_le_mul_of_nonneg_right (c := a.den) bc (Int.ofNat_zero_le _)
    rw [Int.mul_right_comm]  at bc
    have ac := le_trans ab bc
    repeat rw [Int.mul_right_comm _ b.den] at ac
    apply Int.le_of_mul_le_mul_right ac
    have := b.den_pos
    exact Int.ofNat_pos.mpr this

instance : IsDecidableLinearOrder ℚ where
