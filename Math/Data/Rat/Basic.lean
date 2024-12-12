import Math.Data.StdInt.AbsoluteValue
import Math.Data.QuotLike.Basic
import Math.Data.StdNat.Gcd
import Math.Ops.Checked

structure Fract where
  num: Int
  den: Nat
  den_pos: 0 < den := by exact Nat.zero_lt_succ _

def fract_reduce_den {a: Fract} : (‖a.num‖.gcd a.den: Int) ≠ 0 := by
  intro h
  have : ‖a.num‖.gcd a.den = 0 := Int.ofNat.inj h
  have h := Nat.eq_zero_of_gcd_eq_zero_right this
  have := a.den_pos
  rw [h] at this
  contradiction

def Fract.isReduced (a: Fract) : Prop := ‖a.num‖.gcd a.den = 1
def Fract.reduce (a: Fract) : Fract where
  num := a.num / ‖a.num‖.gcd a.den
  den := a.den / ‖a.num‖.gcd a.den
  den_pos := by
    rw [Nat.div_eq, if_pos]
    apply Nat.zero_lt_succ
    apply And.intro
    apply Nat.zero_lt_of_ne_zero
    intro h
    have h := Nat.eq_zero_of_gcd_eq_zero_right h
    have := a.den_pos
    rw [h] at this
    contradiction
    apply Nat.le_of_dvd
    exact a.den_pos
    apply Nat.gcd_dvd_right

def Fract.reduce.isReduced (a: Fract) : a.reduce.isReduced := by
  unfold reduce Fract.isReduced
  simp
  apply Nat.eq_of_mul_eq_mul_right
  show 0 < ‖a.num‖.gcd a.den
  apply Nat.zero_lt_of_ne_zero
  intro h
  have h := Nat.eq_zero_of_gcd_eq_zero_right h
  have := a.den_pos
  rw [h] at this
  contradiction
  rw [←Nat.gcd_mul_right]
  conv => {
    lhs; lhs
    rhs
    rw [←Int.natAbs_ofNat (‖a.num‖.gcd a.den),]
  }
  show (Int.natAbs _ * _).gcd _ = _
  rw [←Int.natAbs_mul, Int.ediv_mul_cancel, Nat.div_mul_cancel, Nat.one_mul]
  rfl
  apply Nat.gcd_dvd_right
  apply Int.dvd_natAbs.mp
  apply Int.ofNat_dvd.mpr
  apply Nat.gcd_dvd_left

structure Rat extends Fract where
  isReduced: toFract.isReduced

notation "ℚ" => Rat

def Rat.toFract.inj (a b: ℚ) : a.toFract = b.toFract -> a = b := by
  intro eq
  cases a; cases b;
  congr

def Fract.den_nz (a: Fract) : Int.ofNat a.den ≠ 0 := by
  cases a  with | mk a d p =>
  dsimp
  intro h
  cases h
  contradiction

def Fract.Equiv (a b: Fract) : Prop := a.num * b.den = b.num * a.den

@[refl]
def Fract.Equiv.refl (a: Fract) : a.Equiv a := rfl
@[symm]
def Fract.Equiv.symm {a b: Fract} : a.Equiv b -> b.Equiv a := Eq.symm
@[symm]
def Fract.Equiv.trans {a b c: Fract} : a.Equiv b -> b.Equiv c -> a.Equiv c := by
  unfold Equiv
  intro ab bc
  have p1 : a.num * c.den * b.den = b.num * a.den * c.den := by rw [Int.mul_right_comm, ab]
  have p2 : a.num * c.den * b.den = c.num * a.den * b.den := by
    rw [Int.mul_right_comm c.num, ←bc, p1]
    ac_rfl
  apply (Int.mul_eq_mul_right_iff _).mp
  assumption
  exact b.den_nz

instance Fract.setoid : Setoid Fract where
  r := Fract.Equiv
  iseqv := ⟨Fract.Equiv.refl, Fract.Equiv.symm, Fract.Equiv.trans⟩

@[refl]
def Fract.refl (a: Fract) : a ≈ a := Fract.Equiv.refl a
@[symm]
def Fract.symm {a b: Fract} : a ≈ b -> b ≈ a := Fract.Equiv.symm
def Fract.trans {a b c: Fract} : a ≈ b -> b ≈ c -> a ≈ c := Fract.Equiv.trans

def Fract.reduce.spec (a: Fract) : a ≈ a.reduce := by
  cases a with | mk n d dpos =>
  show _ * _ = _ * _
  unfold reduce
  dsimp
  rw [←Int.mul_ediv_assoc, Int.mul_comm n, Int.mul_ediv_assoc, Int.mul_comm]
  apply Int.dvd_natAbs.mp
  apply Int.ofNat_dvd.mpr
  apply Nat.gcd_dvd_left
  apply Int.dvd_natAbs.mp
  apply Int.ofNat_dvd.mpr
  apply Nat.gcd_dvd_right

def Fract.isReduced.spec (a b: Fract) : a.isReduced -> b.isReduced -> a ≈ b -> a = b := by
  intro ared bred h
  replace h : _ * _  = _ * _ := h
  cases a with | mk an ad adpos =>
  cases b with | mk bn bd bdpos =>
  unfold isReduced at ared bred
  simp at *
  have sign_eq : (an * bd).sign = (bn * ad).sign := by rw [h]
  rw [Int.sign_mul, Int.sign_mul, Int.sign_ofNat_of_nonzero (Nat.not_eq_zero_of_lt adpos)
    , Int.sign_ofNat_of_nonzero (Nat.not_eq_zero_of_lt bdpos), Int.mul_one, Int.mul_one] at sign_eq
  have val_eq : (an * bd).natAbs = (bn * ad).natAbs := by rw [h]
  rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_ofNat, Int.natAbs_ofNat] at val_eq
  replace val_eq : ‖an‖ * bd = ‖bn‖ * ad := val_eq
  have p1 : ‖bn‖ ∣ ‖an‖ * bd := by exists ad
  replace p1 := Nat.dvd_left_of_dvd_of_gcd_eq_one _ _ _ p1 bred
  have p2 : ‖an‖ ∣ ‖bn‖ * ad := by exists bd; rw [val_eq]
  replace p2 := Nat.dvd_left_of_dvd_of_gcd_eq_one _ _ _ p2 ared
  have an_abs_eq_bn_abs : an.natAbs = bn.natAbs := Nat.dvd_antisymm p2 p1

  have p1 : ad ∣ bd * ‖an‖ := by exists ‖bn‖; rw [Nat.mul_comm, val_eq, Nat.mul_comm]
  replace p1 := Nat.dvd_left_of_dvd_of_gcd_eq_one _ _ _ p1 (Nat.gcd_comm _ _ ▸ ared)
  have p2 : bd ∣ ad * ‖bn‖ := by exists ‖an‖; rw [Nat.mul_comm, ←val_eq, Nat.mul_comm]
  replace p2 := Nat.dvd_left_of_dvd_of_gcd_eq_one _ _ _ p2 (Nat.gcd_comm _ _ ▸ bred)
  cases Nat.dvd_antisymm p2 p1

  rw [←Int.sign_mul_natAbs an, ←Int.sign_mul_natAbs bn]
  rw [an_abs_eq_bn_abs, sign_eq]
  trivial

instance : QuotientLike Fract.setoid ℚ where
  mk a := .mk a.reduce (Fract.reduce.isReduced _)
  unwrapQuot := Rat.toFract
  mk_unwrapQuot := by
    intro q
    cases q with | mk q qred =>
    dsimp
    congr
    apply Fract.isReduced.spec
    apply Fract.reduce.isReduced
    assumption
    symm
    apply Fract.reduce.spec
  ind := by
    intro motive h q
    cases q with | mk q qred =>
    have : q = q.reduce := by
      apply Fract.isReduced.spec
      assumption
      apply Fract.reduce.isReduced
      apply Fract.reduce.spec
    conv in q => { rw [this] }
    apply h
  sound := by
    dsimp
    intro a b r
    congr 1
    apply Fract.isReduced.spec
    apply Fract.reduce.isReduced
    apply Fract.reduce.isReduced
    apply Fract.trans
    symm; apply Fract.reduce.spec
    apply flip Fract.trans
    apply Fract.reduce.spec
    assumption
  exact := by
    intro a b h
    apply Fract.trans
    apply Fract.reduce.spec
    apply flip Fract.trans
    symm; apply Fract.reduce.spec
    rw [Rat.mk.inj h]

local notation "⟦" f "⟧" => QuotLike.mk (Q := ℚ) f

def Fract.add (a b: Fract) : Fract where
  num := a.num * b.den + b.num * a.den
  den := a.den * b.den
  den_pos := Nat.mul_pos a.den_pos b.den_pos

instance : Add Fract := ⟨.add⟩

def Fract.add.spec (a b c d: Fract) : a ≈ c -> b ≈ d -> a + b ≈ c + d := by
  intro ac bd
  replace ac : _ * _ = _ * _ := ac
  replace bd : _ * _ = _ * _ := bd
  show a.add b ≈ c.add d
  unfold add
  show _ * _ = _ * _
  simp [Int.add_mul, Int.mul_assoc]
  rw [Int.mul_left_comm b.den c.den, Int.mul_comm c.den d.den, Int.mul_left_comm a.den d.den,
    ←Int.mul_assoc, ac, ←Int.mul_assoc b.num, bd]
  ac_rfl

def Rat.add : ℚ -> ℚ -> ℚ := by
  apply quot.lift₂ (⟦· + ·⟧)
  intros
  apply quot.sound
  apply Fract.add.spec <;> assumption

instance : Add ℚ := ⟨.add⟩

def Rat.mk_add (a b: Fract) : ⟦a⟧ + ⟦b⟧ = ⟦a + b⟧ := by
  show Rat.add _ _ = _
  exact quot.lift₂_mk

def Fract.mul (a b: Fract) : Fract where
  num := a.num * b.num
  den := a.den * b.den
  den_pos := Nat.mul_pos a.den_pos b.den_pos

instance : Mul Fract := ⟨.mul⟩

@[simp]
def Fract.mul_num (a b: Fract) : (a * b).num = a.num * b.num := rfl
@[simp]
def Fract.mul_den (a b: Fract) : (a * b).den = a.den * b.den := rfl

def Fract.mul.spec (a b c d: Fract) : a ≈ c -> b ≈ d -> a * b ≈ c * d := by
  intro ac bd
  replace ac : _ * _ = _ * _ := ac
  replace bd : _ * _ = _ * _ := bd
  show a.mul b ≈ c.mul d
  unfold mul
  show _ * _ = _ * _
  simp
  rw [Int.mul_assoc, Int.mul_left_comm b.num]
  rw [Int.mul_assoc, Int.mul_left_comm d.num]
  rw [←Int.mul_assoc, ←Int.mul_assoc, ac, ←bd]
  ac_rfl

def Rat.mul : ℚ -> ℚ -> ℚ := by
  apply quot.lift₂ (⟦· * ·⟧)
  intros
  apply quot.sound
  apply Fract.mul.spec <;> assumption

instance : Mul ℚ := ⟨.mul⟩

def Rat.mk_mul (a b: Fract) : ⟦a⟧ * ⟦b⟧ = ⟦a * b⟧ := by
  show Rat.mul _ _ = _
  exact quot.lift₂_mk

def Fract.abs (a: Fract) : Fract where
  num := ‖a.num‖
  den := a.den
  den_pos := a.den_pos

instance : AbsoluteValue Fract Fract := ⟨.abs⟩

@[simp]
def Fract.abs_num (a: Fract) : ‖a‖.num = ‖a.num‖ := rfl
@[simp]
def Fract.abs_den (a: Fract) : ‖a‖.den = a.den := rfl

def Fract.abs.spec (a b: Fract) : a ≈ b -> ‖a‖ ≈ ‖b‖ := by
  intro eqv
  show _ * _ = _ * _
  have : ‖a‖.num = ‖a.num‖ := rfl
  rw [this]
  have : ‖b‖.num = ‖b.num‖ := rfl
  rw [this]
  have : ‖a‖.den = ‖Int.ofNat a.den‖ := rfl
  rw [this]
  have : ‖b‖.den = ‖Int.ofNat b.den‖ := rfl
  rw [this]
  rw [Int.ofNat_mul_ofNat, Int.ofNat_mul_ofNat]
  congr 1
  show Int.natAbs a.num * Int.natAbs b.den = Int.natAbs b.num * Int.natAbs a.den
  rw [←Int.natAbs_mul, eqv, ←Int.natAbs_mul]

def Rat.abs (a: ℚ) : ℚ where
  toFract := a.toFract.abs
  isReduced := by
    unfold Fract.isReduced Fract.abs
    show (Int.natAbs _).gcd _ = 1
    rw [Int.natAbs_ofNat, a.isReduced]

instance : AbsoluteValue ℚ ℚ := ⟨.abs⟩

def Rat.mk_abs (a: Fract) : ‖⟦a⟧‖ = ⟦‖a‖⟧ := by
  apply Rat.toFract.inj
  apply Fract.isReduced.spec
  apply Rat.isReduced
  apply Rat.isReduced
  apply Fract.trans _ (Fract.reduce.spec _)
  apply Fract.abs.spec
  symm
  apply Fract.reduce.spec

def Rat.ofNat (n: Nat) : ℚ where
  num := n
  den := 1
  isReduced := Nat.gcd_eq_right (Nat.one_dvd _)

instance : OfNat ℚ n := ⟨Rat.ofNat n⟩

def Rat.eq_zero_iff_num_eq_zero {a: ℚ} : a = 0 ↔ a.num = 0 := by
  apply Iff.intro
  intro h
  cases h; rfl
  intro h
  cases a with | mk a red =>
  simp at h
  cases a with | mk a d =>
  simp at *
  subst h
  unfold Fract.isReduced at red
  simp at red
  replace red : Nat.gcd 0 d = 1 := red
  rw [Nat.gcd_zero_left] at red
  subst d
  rfl

def Rat.inv (a: ℚ) (h: a ≠ 0) : ℚ where
  num := a.den
  den := ‖a.num‖
  den_pos := by
    apply Nat.zero_lt_of_ne_zero
    intro g
    apply h
    apply Rat.eq_zero_iff_num_eq_zero.mpr
    apply Int.natAbs_eq_zero.mp
    assumption
  isReduced := by
    unfold Fract.isReduced
    simp
    show (Int.natAbs _).gcd _ = 1
    rw [Int.natAbs_ofNat, Nat.gcd_comm]
    exact a.isReduced

instance : CheckedInvert ℚ (fun q => q ≠ 0) where
  checked_invert := Rat.inv

def Rat.div (a b: ℚ) (h: b ≠ 0) : ℚ := a * b⁻¹

instance : CheckedDiv ℚ (fun q => q ≠ 0) where
  checked_div := Rat.div

def Rat.abs_mul (a b: ℚ) : ‖a * b‖ = ‖a‖ * ‖b‖ := by
  quot_ind (a b)
  simp [mk_mul, mk_abs]
  apply quot.sound
  show _ * _ = _ * _
  simp
  repeat rw [Int.ofNat_mul_ofNat]
  congr
  exact Int.natAbs_mul _ _
