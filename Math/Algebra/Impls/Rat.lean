import Math.Algebra.Basic
import Math.Algebra.GroupWithZero.Basic
import Math.Algebra.Field.Defs
import Math.Algebra.Semiring.Char
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

instance : IsAddMonoidWithOne ℚ := inferInstance
instance : IsGroupWithZero ℚ := inferInstance
instance : IsRing ℚ := inferInstance

def Rat.char_eq : char Rat = 0 := by
  apply char_eq_of_natCast_eq_zero
  rfl
  intro m h
  cases h
  apply Nat.dvd_refl

class RatCast (α: Type u) where
  cast: ℚ -> α

attribute [coe] RatCast.cast

instance [RatCast α] : Coe ℚ α where
  coe := RatCast.cast

class IsRatAlgebra (α: Type u) [FieldOps α] [RatCast α] [SMul ℚ α] extends IsField α where
  rsmul_eq_cast_mul (q: ℚ) (a: α) : q • a = q * a
  eq_zero_of_natCast_eq_zero (n: ℕ): (n: α) = 0 -> n = 0
  ratCast_eq_intCast_div?_natCast (q: ℚ): (q: α) = (q.num /? q.den ~((Nat.ne_of_lt' q.den_pos <| eq_zero_of_natCast_eq_zero _ ·)): α)

export IsRatAlgebra (
  rsmul_eq_cast_mul
  eq_zero_of_natCast_eq_zero
  ratCast_eq_intCast_div?_natCast
)

instance : RatCast ℚ where
  cast := id

instance : IsRatAlgebra ℚ where
  rsmul_eq_cast_mul _ _ := rfl
  eq_zero_of_natCast_eq_zero := by
    intro n h
    cases h
    rfl
  ratCast_eq_intCast_div?_natCast q := by
    show q = _
    rw [div?_eq_mul_inv?]
    show q = (Rat.mk (Fract.mk q.num 1 _) _).mul ((Rat.mk (Fract.mk q.den 1 _) _).inv _)
    rw [Rat.inv]
    dsimp
    conv => {
      rhs; rhs; lhs; arg 1
      rw [Int.sign_ofNat_of_nonzero (by
        have := q.den_pos
        intro h; rw [h] at this
        contradiction), Int.one_mul]
    }
    show q = Rat.mk ((Fract.mk _ _ _).mul (Fract.mk _ _ _)).reduce _
    show q = Rat.mk ((Fract.mk _ _ _)).reduce _
    cases q with | mk q hq =>
    congr; dsimp
    rw [Fract.isReduced.spec (Fract.mk (q.num * 1) (1 * ‖(q.den: Int)‖) _).reduce (Fract.mk q.num q.den _)]
    apply Fract.reduce.isReduced
    assumption
    apply Fract.trans; symm
    apply Fract.reduce.spec
    show _ = _
    dsimp
    rw [Int.mul_one, Nat.one_mul]
    rfl

def char_eq_zero_of_ratAlg [FieldOps α] [RatCast α] [SMul ℚ α] [IsRatAlgebra α] : char α = 0 := by
  apply char_eq_of_natCast_eq_zero
  rw [natCast_zero]
  intro n h
  rw [eq_zero_of_natCast_eq_zero _ h]
  apply Nat.dvd_refl

def intCast_div?_natCast_eq_ratCast_mk
  [FieldOps α] [RatCast α] [SMul ℚ α] [IsRatAlgebra α]
  (a: Int) (b: Nat) (h: b ≠ 0) :
  (a: α) /? (b: α) ~(by
    intro g
    have := eq_zero_of_natCast_eq_zero _ g
    contradiction) = (Rat.mk (Fract.mk a b (by
    apply Nat.zero_lt_of_ne_zero h)).reduce (Fract.reduce.isReduced _)) := by
  let x := Int.gcd a b
  have x_dvd_a : (x: Int) ∣ a := Int.gcd_dvd_left (a := a) (b := b)
  have x_dvd_b : x ∣ b := Int.ofNat_dvd.mp (Int.gcd_dvd_right (a := a) (b := b))
  obtain ⟨a', ha⟩ := x_dvd_a
  obtain ⟨b', hb⟩ := x_dvd_b
  rw [ha, intCast_mul]
  conv => { lhs; arg 2; rw [hb, natCast_mul, ←intCast_ofNat, ←intCast_ofNat] }
  conv => { rhs; arg 1; arg 1; arg 1; arg 2; rw [hb] }
  rw [div?_eq_mul_inv?, inv?_mul_rev, mul_assoc, mul_right_comm (a': α), ←mul_comm (a': α),
    ←mul_assoc, mul_inv?_cancel, one_mul, ←div?_eq_mul_inv?]
  unfold Fract.reduce
  dsimp
  have int_abs_def : ∀x: Int, ‖x‖ = x.natAbs := fun _ => rfl
  conv => {
    rhs; arg 1; arg 1
    conv => {
      arg 1
      rw [int_abs_def, Int.natAbs_mul, Int.natAbs_ofNat, ←int_abs_def,
        Nat.gcd_mul_left, Int.natCast_mul, Int.mul_ediv_mul_of_pos _ _ (by
          refine Int.ofNat_pos.mpr ?_
          apply Nat.pos_of_ne_zero
          intro h; rw [h, Nat.zero_mul] at hb
          contradiction)]
    }
    arg 2
    rw [int_abs_def, Int.natAbs_mul, Int.natAbs_ofNat, ←int_abs_def,
      Nat.gcd_mul_left, Nat.mul_div_mul_left _ _ (by
        apply Nat.pos_of_ne_zero
        intro h; rw [h, Nat.zero_mul] at hb
        contradiction)]
  }
  rw [ratCast_eq_intCast_div?_natCast]
  dsimp
  suffices ‖a'‖.gcd b' = 1 by
    congr
    rw [this, Int.ofNat_one, Int.ediv_one]
    rw [this, Nat.div_one]
    rw [intCast_ofNat]
  apply Nat.eq_of_mul_eq_mul_left
  show 0 < x
  apply Nat.pos_of_ne_zero
  intro h; rw [h, Nat.zero_mul] at hb
  contradiction
  rw [←Nat.gcd_mul_left, ←hb]
  conv => {
    lhs; rw [←Int.natAbs_ofNat x, int_abs_def, ←Int.natAbs_mul, ←int_abs_def, ←ha]
  }
  rw [Nat.mul_one]; rfl
  rw [intCast_ofNat]
  intro h
  cases eq_zero_of_natCast_eq_zero _ h
  rw [Nat.mul_zero] at hb
  contradiction
  rw [intCast_ofNat]
  intro h
  have := eq_zero_of_natCast_eq_zero _ h
  rw [this, Nat.zero_mul] at hb
  contradiction

instance [FieldOps α] [RatCast α] [SMul ℚ α] [IsRatAlgebra α] : AlgebraMap ℚ α where
  toFun a := a
  resp_zero := by
    dsimp
    erw [ratCast_eq_intCast_div?_natCast, intCast_zero, div?_eq_mul_inv?, zero_mul]
  resp_one := by
    dsimp
    erw [ratCast_eq_intCast_div?_natCast, intCast_one, div?_eq_mul_inv?, one_mul]
    symm
    apply inv?_eq_of_mul_right
    rw [one_mul]
    apply natCast_one
  resp_mul := by
    intro a b
    dsimp
    rw [ratCast_eq_intCast_div?_natCast a, ratCast_eq_intCast_div?_natCast b,
      div?_eq_mul_inv?, div?_eq_mul_inv?, mul_assoc,
      ←mul_assoc ((a.den: α)⁻¹?~(_)), mul_comm _ (b.num: α),
      ←mul_assoc, ←mul_assoc, mul_assoc, ←inv?_mul_rev, ←div?_eq_mul_inv?]
    conv => {
      rhs; rw [←intCast_mul]
      arg 2; rw [←natCast_mul, Nat.mul_comm]
    }
    rw [intCast_div?_natCast_eq_ratCast_mk]
    rfl
    intro g
    cases Nat.mul_eq_zero.mp g
    have := a.den_nz
    contradiction
    have := b.den_nz
    contradiction
  resp_add := by
    intro x y
    dsimp
    rw [ratCast_eq_intCast_div?_natCast x, ratCast_eq_intCast_div?_natCast y]
    rw [div?_eq_mul_inv?, div?_eq_mul_inv?]
    conv => {
      rhs; conv => { lhs; rw [←one_mul (_ * _), ←mul_inv?_cancel (y.den: α) (by
        intro h
        exact y.den_nz (eq_zero_of_natCast_eq_zero _ h))] }
      rhs; rw [←mul_one (_ * _), ←mul_inv?_cancel (x.den: α) (by
        intro h
        exact x.den_nz (eq_zero_of_natCast_eq_zero _ h))]
    }
    rw [mul_assoc, mul_left_comm _ (x.num: α), ←mul_assoc, ←inv?_mul_rev]
    rw [mul_assoc (y.num: α), mul_left_comm _ (x.den: α), ←mul_assoc, ←inv?_mul_rev]
    rw [←add_mul, ←div?_eq_mul_inv?]
    conv => { rhs; arg 1; rw [←intCast_ofNat, ←intCast_ofNat] }
    conv => { rhs; arg 2; rw [←natCast_mul] }
    rw [←intCast_mul, ←intCast_mul, ←intCast_add, intCast_div?_natCast_eq_ratCast_mk]
    congr
    cases x with | mk x hx =>
    cases y with | mk y hy =>
    apply Rat.toFract.inj
    apply Fract.isReduced.spec
    apply Rat.isReduced
    apply Rat.isReduced
    apply flip Fract.trans
    apply Fract.reduce.spec
    apply Fract.trans
    symm; apply Fract.reduce.spec
    show x + y ≈ _
    show _ = _
    simp
    ac_rfl
    intro a b
    intro h
    cases Nat.mul_eq_zero.mp h
    apply b.den_nz; assumption
    apply a.den_nz; assumption

instance [FieldOps α] [RatCast α] [SMul ℚ α] [IsRatAlgebra α] : IsAlgebra ℚ α where
  commutes _ _ := by rw [mul_comm]
  smul_def := rsmul_eq_cast_mul
