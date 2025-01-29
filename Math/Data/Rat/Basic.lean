import Math.Data.QuotLike.Basic
import Math.Data.StdNat.Gcd
import Math.Data.StdInt.Basic
import Math.Ops.Checked
import Math.Ops.Abs

structure Fract where
  num: Int
  den: Nat
  den_pos: 0 < den := by exact Nat.zero_lt_succ _
deriving Repr, DecidableEq

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
deriving Repr, DecidableEq

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

instance (a b: Fract) : Decidable (a ≈ b) := inferInstanceAs (Decidable ((_: Int) = _))

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

@[simp]
def Fract.add_num (a b: Fract) : (a + b).num = a.num * b.den + b.num * a.den := rfl
@[simp]
def Fract.add_den (a b: Fract) : (a + b).den = a.den * b.den := rfl

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

@[simp]
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

@[simp]
def Rat.mk_mul (a b: Fract) : ⟦a⟧ * ⟦b⟧ = ⟦a * b⟧ := by
  show Rat.mul _ _ = _
  exact quot.lift₂_mk

def Fract.neg (a: Fract) : Fract where
  num := -a.num
  den := a.den
  den_pos := a.den_pos

instance : Neg Fract := ⟨.neg⟩

@[simp]
def Fract.neg_num (a: Fract) : (-a).num = -a.num := rfl
@[simp]
def Fract.neg_den (a: Fract) : (-a).den = a.den := rfl

def Fract.neg.spec (a b: Fract) : a ≈ b -> -a ≈ -b := by
  intro ab
  show _ * _ = _ * _
  simp
  rw [ab]

def Rat.neg (a: ℚ) : ℚ where
  toFract := -a.toFract
  isReduced := by
    unfold toFract Fract.isReduced
    simp
    show (Int.natAbs _).gcd _ = _
    rw [Int.natAbs_neg]
    exact a.isReduced

instance : Neg ℚ := ⟨.neg⟩

@[simp]
def Rat.neg_num (a: ℚ) : (-a).num = -a.num := rfl
@[simp]
def Rat.neg_den (a: ℚ) : (-a).den = a.den := rfl

@[simp]
def Rat.mk_neg (a: Fract) : -⟦a⟧ = ⟦-a⟧ := by
  apply Rat.toFract.inj
  apply Fract.isReduced.spec
  apply Rat.isReduced
  apply Rat.isReduced
  apply Fract.trans _ (Fract.reduce.spec _)
  apply Fract.neg.spec
  symm
  apply Fract.reduce.spec

def Fract.sub (a b: Fract) : Fract where
  num := a.num * b.den - b.num * a.den
  den := a.den * b.den
  den_pos := Nat.mul_pos a.den_pos b.den_pos

instance : Sub Fract := ⟨.sub⟩

@[simp]
def Fract.sub_num (a b: Fract) : (a - b).num = a.num * b.den - b.num * a.den := rfl
@[simp]
def Fract.sub_den (a b: Fract) : (a - b).den = a.den * b.den := rfl

def Fract.sub_eq_add_neg (a b: Fract) : a - b = a + -b := by
  cases a; cases b
  show sub _ _ = add _ (neg _)
  unfold sub add neg
  simp
  rw [Int.sub_eq_add_neg]

def Rat.sub : ℚ -> ℚ -> ℚ := by
  apply quot.lift₂ (⟦· - ·⟧)
  intros _ _ _ _ ac bd
  simp only [Fract.sub_eq_add_neg, ←mk_neg, ←mk_add]
  rw [quot.sound ac, quot.sound bd]

instance : Sub ℚ := ⟨.sub⟩

@[simp]
def Rat.mk_sub (a b: Fract) : ⟦a⟧ - ⟦b⟧ = ⟦a - b⟧ := by
  show sub _ _ = ⟦Fract.sub _ _⟧
  exact quot.lift₂_mk

def Rat.sub_eq_add_neg (a b: ℚ) : a - b = a + -b := by
  quot_ind (a b)
  simp
  rw [Fract.sub_eq_add_neg]

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

@[simp]
def Rat.abs_num (a: ℚ) : ‖a‖.num = ‖a.num‖ := rfl
@[simp]
def Rat.abs_den (a: ℚ) : ‖a‖.den = a.den := rfl

@[simp]
def Rat.mk_abs (a: Fract) : ‖⟦a⟧‖ = ⟦‖a‖⟧ := by
  apply Rat.toFract.inj
  apply Fract.isReduced.spec
  apply Rat.isReduced
  apply Rat.isReduced
  apply Fract.trans _ (Fract.reduce.spec _)
  apply Fract.abs.spec
  symm
  apply Fract.reduce.spec

def Fract.ofNat (n: Nat) : Fract where
  num := n
  den := 1

def Rat.ofNat (n: Nat) : ℚ where
  toFract := Fract.ofNat n
  isReduced := Nat.gcd_eq_right (Nat.one_dvd _)

instance : OfNat Fract n := ⟨Fract.ofNat n⟩
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

def Fract.inv (a: Fract) (h: ¬a ≈ 0) : Fract where
  num := a.num.sign * a.den
  den := ‖a.num‖
  den_pos := by
    apply Nat.zero_lt_of_ne_zero
    intro g
    apply h
    apply quot.exact (Q := ℚ)
    apply Rat.eq_zero_iff_num_eq_zero.mpr
    apply Int.natAbs_eq_zero.mp
    simp
    apply Rat.eq_zero_iff_num_eq_zero.mp
    show _ = ⟦0⟧
    apply quot.sound
    obtain ⟨n, d, dpos⟩  := a
    simp at g
    cases Int.natAbs_eq_zero.mp g
    show _ * _ = _ * _
    erw [Int.zero_mul, Int.zero_mul]

def Rat.inv (a: ℚ) (h: a ≠ 0) : ℚ where
  num := a.num.sign * a.den
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
    rw [Int.natAbs_mul, Int.natAbs_sign, if_neg, Nat.one_mul,
      Int.natAbs_ofNat, Nat.gcd_comm]
    exact a.isReduced
    intro g; apply h
    apply Rat.eq_zero_iff_num_eq_zero.mpr
    assumption

instance : CheckedInvert Fract (fun q => ¬q ≈ 0) where
  checked_invert := Fract.inv
instance : CheckedInvert ℚ (fun q => q ≠ 0) where
  checked_invert := Rat.inv

@[simp]
def Fract.inv.num (a: Fract) (h: ¬a ≈ 0) : (a⁻¹?).num = a.num.sign * a.den := rfl
@[simp]
def Fract.inv.den (a: Fract) (h: ¬a ≈ 0) : (a⁻¹?).den = ‖a.num‖ := rfl

@[simp]
def Rat.eqv_nonzero (a: Fract) (h: ¬a ≈ 0) : ⟦a⟧ ≠ 0 := by
  intro g
  apply h
  apply quot.exact (Q := ℚ)
  assumption

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply Rat.eqv_nonzero <;> assumption)

def Fract.div (a b: Fract) (h: ¬b ≈ 0) : Fract := a * b⁻¹?
def Rat.div (a b: ℚ) (h: b ≠ 0) : ℚ := a * b⁻¹?

instance : CheckedDiv Fract (fun q => ¬q ≈ 0) where
  checked_div := Fract.div

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

instance : Inhabited ℚ := ⟨0⟩

def Fract.sign (q: Fract) : Int := q.num.sign

def Fract.sign.spec (a b: Fract) : a ≈ b -> a.sign = b.sign := by
  intro eq
  cases a with | mk an ad ad_pos =>
  cases b with | mk bn bd bd_pos =>
  simp [sign]
  replace eq : _ * _ = _ * _ := eq
  simp at *
  cases an with
  | ofNat an =>
    cases bn with
    | ofNat bn =>
      cases an; cases bn
      rfl
      erw [Int.ofNat_mul_ofNat, Int.ofNat_mul_ofNat,
        Nat.zero_mul] at eq
      replace eq := Int.ofNat.inj eq
      cases Nat.mul_eq_zero.mp eq.symm
      contradiction
      subst ad
      contradiction
      cases bn
      erw [Int.ofNat_mul_ofNat, Int.ofNat_mul_ofNat,
        Nat.zero_mul] at eq
      replace eq := Int.ofNat.inj eq
      cases Nat.mul_eq_zero.mp eq
      contradiction
      subst bd
      contradiction
      rfl
    | negSucc bn =>
      cases ad
      contradiction
      erw [Int.ofNat_mul_ofNat, Int.negSucc_mul_ofNat] at eq
      contradiction
  | negSucc an =>
    cases bn with
    | negSucc bn => rfl
    | ofNat bn =>
      cases bd
      contradiction
      erw [Int.ofNat_mul_ofNat, Int.negSucc_mul_ofNat] at eq
      contradiction

def Rat.sign (q: ℚ) : Int := q.num.sign

@[simp]
def Rat.mk_sign (a: Fract) : ⟦a⟧.sign = a.sign := by
  apply Fract.sign.spec
  symm; apply Fract.reduce.spec

def Rat.abs_sign (a: ℚ) : ‖a‖.sign = ‖a.sign‖ := by
  obtain ⟨⟨a, _, _ ⟩, _⟩ := a
  cases a using Int.cases <;> rfl

def Rat.neg_sign (a: ℚ) : (-a).sign = -a.sign := by
  obtain ⟨⟨a, _, _ ⟩, _⟩ := a
  cases a using Int.cases <;> rfl

def Fract.inv.spec (a b: Fract) (h₀: ¬a ≈ 0) (h₁: ¬b ≈ 0) : a ≈ b -> a⁻¹? ≈ b⁻¹? := by
  intro eq
  have : a.num.sign = b.num.sign := by
    have : ⟦a⟧ = ⟦b⟧ := quot.sound eq
    have : ⟦a⟧.sign = ⟦b⟧.sign :=  by rw [this]
    simp at this
    assumption
  replace eq : _ * _ = _ * _ := eq
  show _ * _ = _ * _
  simp
  show _ * (Int.natAbs _: Int) = _ * (Int.natAbs _: Int)
  rw [Int.mul_right_comm, this, Int.sign_mul_natAbs]
  rw [Int.mul_right_comm, ←this, Int.sign_mul_natAbs]
  exact eq.symm

@[simp]
def Rat.mk_inv (a: Fract) (h: ¬a ≈ 0)  :
  ⟦a⟧⁻¹? = ⟦a⁻¹?⟧ := by
  apply Rat.toFract.inj
  apply Fract.isReduced.spec
  apply Rat.isReduced
  apply Rat.isReduced
  apply Fract.trans _ (Fract.reduce.spec _)
  apply Fract.inv.spec
  intro g
  apply h
  exact (Fract.reduce.spec _).trans g
  symm; apply Fract.reduce.spec

@[simp]
def Rat.mk_div (a b: Fract) (h: ¬b ≈ 0) : ⟦a⟧ /? ⟦b⟧ = ⟦a /? b⟧ := by
  show _ * _ = ⟦_ * _⟧
  rw [mk_inv]
  simp
  assumption

def Rat.approx_sqrt_aux (n x: ℚ) : Nat -> ℚ
| 0 => x
| .succ m =>
  if h:x = 0 then
    0
  else
    Rat.approx_sqrt_aux n ((x + n /? x) /? (2: ℚ)) m

def Rat.approx_sqrt (a: ℚ) : Nat -> ℚ := a.approx_sqrt_aux a

@[simp]
def Rat.neg_neg (a: ℚ) : - -a = a := by
  obtain ⟨⟨n, d, d_pos⟩, _⟩ := a
  simp [Neg.neg, Rat.neg, Fract.neg]
  exact Int.neg_neg n

def Rat.eq_zero_of_num_eq_zero {a: ℚ} : a = 0 ↔ a.num = 0 := by
  apply Iff.intro
  intro h; subst h; rfl
  intro h
  obtain ⟨⟨n, d, d_pos⟩, red⟩ := a
  congr
  simp [Fract.isReduced] at red
  simp at h
  erw [h, Nat.gcd_zero_left] at red
  assumption

def Rat.eq_zero_iff_abs_eq_zero {a: ℚ} : a = 0 ↔ ‖a‖ = 0 := by
  apply Iff.intro
  intro h; subst h; rfl
  intro h
  have ⟨h, g⟩  := Fract.mk.inj (Rat.mk.inj h)
  have := Int.natAbs_eq_zero.mp (Int.ofNat.inj h)
  apply eq_zero_of_num_eq_zero.mpr
  assumption

def Rat.congr {a b: ℚ} : a.num = b.num -> a.den = b.den -> a = b := by
  intro numeq deneq
  obtain ⟨⟨n, d, d_pos⟩, red⟩ := a
  obtain ⟨⟨n, d, d_pos⟩, red⟩ := b
  congr

def Rat.neg_add (a b: ℚ) : -(a + b) = -a + -b := by
  quot_ind (a b)
  simp
  apply quot.sound
  show _ * _ = _ * _
  simp [Int.add_mul, Int.neg_add]

def Rat.neg_sub (a b: ℚ) : -(a - b) = b - a := by
  quot_ind (a b)
  simp
  apply quot.sound
  show _ * _ = _ * _
  simp [Int.sub_mul, Int.neg_sub, Int.mul_comm b.den]

def Rat.neg_mul_left (a b: ℚ) : -(a * b) = -a * b := by
  quot_ind (a b)
  simp
  apply quot.sound
  show _ * _ = _ * _
  simp

def Rat.neg_mul_right (a b: ℚ) : -(a * b) = a * -b := by
  quot_ind (a b)
  simp
  apply quot.sound
  show _ * _ = _ * _
  simp

def Rat.add_comm (a b: ℚ) : a + b = b + a := by
  quot_ind (a b)
  simp
  apply quot.sound
  show _ * _ = _ * _
  simp
  ac_rfl

def Rat.add_assoc (a b c: ℚ) : a + b + c = a + (b + c) := by
  quot_ind (a b c)
  simp
  apply quot.sound
  show _ * _ = _ * _
  simp [Int.add_mul]
  ac_rfl

def Rat.mul_comm (a b: ℚ) : a * b = b * a := by
  quot_ind (a b)
  simp
  apply quot.sound
  show _ * _ = _ * _
  simp
  ac_rfl

def Rat.mul_assoc (a b c: ℚ) : a * b * c = a * (b * c) := by
  quot_ind (a b c)
  simp
  apply quot.sound
  show _ * _ = _ * _
  simp [Int.add_mul]
  ac_rfl

def Rat.div_eq_mul_inv (a b: ℚ) (h: b ≠ 0) : a /? b = a * b⁻¹? := rfl

def Rat.mul_div_assoc (a b c: ℚ) (h: c ≠ 0) : a * b /? c = a * (b /? c) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]

instance : @Std.Commutative ℚ (· + ·) := ⟨Rat.add_comm⟩
instance : @Std.Associative ℚ (· + ·) := ⟨Rat.add_assoc⟩
instance : @Std.Commutative ℚ (· * ·) := ⟨Rat.mul_comm⟩
instance : @Std.Associative ℚ (· * ·) := ⟨Rat.mul_assoc⟩

def Rat.add_zero (a: ℚ) : a + 0 = a := by
  quot_ind a
  have : (0: ℚ) = ⟦0⟧ := rfl
  rw [this]
  simp
  apply quot.sound
  show _ * _ = _ * _
  simp
  erw [Int.mul_one, Int.mul_one, Int.zero_mul, Int.add_zero]

def Rat.zero_add (a: ℚ) : 0 + a = a := by
  rw [add_comm, add_zero]

def Rat.mul_zero (a: ℚ) : a * 0 = 0 := by
  quot_ind a
  have : (0: ℚ) = ⟦0⟧ := rfl
  rw [this]
  simp
  apply quot.sound
  show _ * _ = _ * _
  simp
  erw [Int.mul_one, Int.mul_one, Int.zero_mul, Int.mul_zero]

def Rat.zero_mul (a: ℚ) : 0 * a = 0 := by
  rw [mul_comm, mul_zero]

def Rat.mul_one (a: ℚ) : a * 1 = a := by
  quot_ind a
  have : (1: ℚ) = ⟦1⟧ := rfl
  rw [this]
  simp
  apply quot.sound
  show _ * _ = _ * _
  simp
  erw [Int.mul_one, Int.mul_one]

def Rat.one_mul (a: ℚ) : 1 * a = a := by
  rw [mul_comm, mul_one]

def Rat.add_neg_self (a: ℚ) : a + -a = 0 := by
  quot_ind a
  simp
  show _ = ⟦0⟧
  apply quot.sound
  show _ * _ = _ * _
  simp
  erw [Int.zero_mul, Int.mul_one, ←Int.sub_eq_add_neg, Int.sub_self]

def Rat.neg_self_add (a: ℚ) : -a + a = 0 := by
  rw [add_comm, add_neg_self]

def Rat.sub_self (a: ℚ) : a - a = 0 := by
  rw [sub_eq_add_neg, add_neg_self]

def Rat.add_cancel_left {a b k: ℚ} : a = b ↔ k + a = k + b := by
  apply Iff.intro
  intro eq; rw [eq]
  intro eq
  have : -k + (k + a) = -k + (k + b) := by rw [eq]
  iterate 2 rw [←add_assoc, neg_self_add, zero_add] at this
  assumption

def Rat.add_cancel_right {a b k: ℚ} : a = b ↔ a + k = b + k := by
  rw [add_comm _ k, add_comm _ k, add_cancel_left]

def Rat.eq_zero_of_eq_neg_self (a: ℚ) : a = -a -> a = 0 := by
  intro h
  obtain ⟨⟨n, d, dpos⟩, red⟩ := a
  simp [Neg.neg, neg, Fract.neg] at h
  simp [Fract.isReduced] at red
  suffices n = 0 by
    erw [this, Nat.gcd_zero_left] at red
    congr
  clear red dpos d
  cases n with
  | negSucc n => contradiction
  | ofNat n =>
    cases n
    rfl
    contradiction

def Rat.abs_neg (a: ℚ) : ‖-a‖ = ‖a‖ := by
  quot_ind a
  simp
  apply quot.sound
  show _ * _ = _ * _
  simp
  show ↑(Int.natAbs (-a.num)) * (a.den: Int) = _ * _
  rw [Int.natAbs_neg]
  rfl

def Rat.abs_sub_comm (a b: ℚ) : ‖a - b‖ = ‖b - a‖ := by
  rw [←neg_sub, abs_neg]

def Rat.mul_inv_self (a: ℚ) (h: a ≠ 0) : a * a⁻¹? = 1 := by
  quot_ind a
  have : ¬a ≈ 0 := fun g => h (quot.sound g)
  simp [mk_inv _ this]
  show _ = ⟦1⟧
  apply quot.sound
  show _ * _ = _ * _
  simp
  erw [Int.one_mul, Int.mul_one, ←Int.mul_assoc, Int.mul_sign, Int.mul_comm]
  rfl

def Rat.inv_self_mul (a: ℚ) (h: a ≠ 0) : a⁻¹? * a = 1 := by
  rw [mul_comm, mul_inv_self]

def Rat.div_self (a: ℚ) (h: a ≠ 0) : a /? a = 1 := by
  rw [div_eq_mul_inv, mul_inv_self]

def Rat.add_mul (a b k: ℚ) : (a + b) * k = a * k + b * k := by
  quot_ind (a b k)
  simp
  apply quot.sound
  show _ * _ = _ * _
  simp [Int.add_mul]
  ac_rfl

def Rat.mul_add (a b k: ℚ) : k * (a + b) = k * a + k * b := by
  repeat rw [mul_comm k]
  rw [add_mul]

def Rat.sub_mul (a b k: ℚ) : (a - b) * k = a * k - b * k := by
  iterate 2 rw [sub_eq_add_neg]
  rw [add_mul, neg_mul_left]

def Rat.mul_sub (a b k: ℚ) : k * (a - b) = k * a - k * b := by
  repeat rw [mul_comm k]
  rw [sub_mul]

def Rat.mul_two (a: ℚ) : 2 * a = a + a := by
  have : (2: ℚ) = 1 + 1 := rfl
  rw [this, add_mul, one_mul]

def Rat.mul_div_cancel (a b: ℚ) (h: a ≠ 0) : a * (b /? a) = b := by
  rw [div_eq_mul_inv, mul_comm a, mul_assoc, inv_self_mul, mul_one]

def Rat.neg_sub_neg (a b: ℚ) : -a - -b = b - a := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_comm, neg_neg]

def Rat.sub_zero (a: ℚ) : a - 0 = a := by erw [sub_eq_add_neg, add_zero]
def Rat.zero_sub (a: ℚ) : 0 - a = -a := by rw [sub_eq_add_neg, zero_add]

def Rat.mul_cancel_right {a b k: ℚ} (h: k ≠ 0) : a = b ↔  a * k = b * k := by
  apply Iff.intro
  intro g; rw [g]
  intro g
  have : (a * k) * k⁻¹? = (b * k) * k⁻¹? := by rw [g]
  rwa [mul_assoc, mul_assoc, mul_inv_self, mul_one, mul_one] at this

def Rat.mul_cancel_left {a b k: ℚ} (h: k ≠ 0) : a = b ↔ k * a = k * b := by
  rw [mul_comm k, mul_comm k]
  exact mul_cancel_right h

def Rat.mul_nonzero (a b: ℚ) (ha: a ≠ 0) (hb: b ≠ 0) : a * b ≠ 0 := by
  intro h
  replace h : a * b = ⟦0⟧ := h
  replace ha : a ≠ ⟦0⟧ := ha
  replace hb : b ≠ ⟦0⟧ := hb
  quot_ind (a b)
  simp at h
  replace h : _ * _ = _ * _ := quot.exact (Q := ℚ) h
  erw [Int.mul_one, Int.zero_mul] at h
  cases Int.mul_eq_zero.mp h <;> rename_i h
  apply ha; apply quot.sound
  show _ * _ = _ * _
  erw [h, Int.zero_mul, Int.zero_mul]
  apply hb; apply quot.sound
  show _ * _ = _ * _
  erw [h, Int.zero_mul, Int.zero_mul]

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply Rat.mul_nonzero <;> invert_tactic)

def Rat.inv_add_inv (a b: ℚ) (ha: a ≠ 0) (hb: b ≠ 0) :
  a⁻¹? + b⁻¹? = (a + b) /? (a * b) := by
  apply (mul_cancel_right _).mpr
  conv => { rhs; rw [mul_comm, mul_div_cancel] }
  rw [add_mul]
  suffices (a⁻¹? * a) * b + (b⁻¹? * b) * a = a + b by
    rw [←this]
    ac_rfl
  rw [inv_self_mul, inv_self_mul, one_mul, one_mul, add_comm]
  invert_tactic

def Rat.neg_nonzero (a: ℚ) : a ≠ 0 -> (-a) ≠ 0 := by
  intro h g
  apply h
  rw [←neg_neg a, g]
  rfl

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply Rat.neg_nonzero <;> invert_tactic)

def Rat.neg_inv (a: ℚ) (h: a ≠ 0) : -a⁻¹? = (-a)⁻¹? := by
  apply (mul_cancel_left (k := (-a)) _).mpr
  rw [←neg_mul_right, ←neg_mul_left, mul_inv_self, mul_inv_self, neg_neg]
  invert_tactic

def Rat.inv_sub_inv (a b: ℚ) (ha: a ≠ 0) (hb: b ≠ 0) :
  a⁻¹? - b⁻¹? = (b - a) /? (a * b) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, neg_inv, inv_add_inv,
    div_eq_mul_inv, div_eq_mul_inv, ←sub_eq_add_neg, ←neg_sub,
    ←neg_mul_left, neg_mul_right, sub_eq_add_neg, neg_inv]
  congr
  rw [neg_mul_right, neg_neg]

def Rat.abs_nonzero (a: ℚ) : a ≠ 0 -> ‖a‖ ≠ 0 := by
  intro h g
  apply h
  apply eq_zero_iff_abs_eq_zero.mpr
  assumption

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply Rat.abs_nonzero <;> invert_tactic)

def Rat.abs_inv (a: ℚ) (ha: a ≠ 0)  : ‖a⁻¹?‖ = ‖a‖⁻¹? := by
  apply (mul_cancel_left _).mpr
  rw [mul_inv_self ‖a‖, ←abs_mul, mul_inv_self]
  rfl
  invert_tactic

def Rat.abs_div (a b: ℚ) (hb: b ≠ 0) : ‖a /? b‖ = ‖a‖ /? ‖b‖ := by
  rw [div_eq_mul_inv, div_eq_mul_inv, abs_mul, abs_inv]

def Rat.inv_mul (a b: ℚ) (ha: a ≠ 0) (hb: b ≠ 0) : (a * b)⁻¹? = a⁻¹? * b⁻¹? := by
  apply (mul_cancel_left _).mpr
  rw [mul_inv_self]
  suffices 1 = a * a⁻¹? * (b * b⁻¹?) by rw [this]; ac_rfl
  rw [mul_inv_self, mul_inv_self, mul_one]
  invert_tactic

def Rat.inv_nonzero (a: ℚ) (ha: a ≠ 0) : a⁻¹? ≠ 0 := by
  intro h
  apply ha
  have := eq_zero_of_num_eq_zero.mp h
  rcases Int.mul_eq_zero.mp this with azero | denzero
  have := Int.sign_eq_zero_iff_zero.mp azero
  apply eq_zero_of_num_eq_zero.mpr
  assumption
  have := a.den_pos
  rw [Int.ofNat_eq_zero.mp denzero] at this
  contradiction

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply Rat.inv_nonzero <;> invert_tactic)

def Rat.div_nonzero (a b: ℚ) (ha: a ≠ 0) (hb: b ≠ 0) : a /? b ≠ 0 := by
  rw [div_eq_mul_inv]
  invert_tactic

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply Rat.div_nonzero <;> invert_tactic)

def Fract.npow (a: Fract) (n: Nat) : Fract where
  num := a.num ^ n
  den := a.den ^ n
  den_pos := by
    refine Nat.pos_pow_of_pos n ?_
    exact a.den_pos

instance : Pow Fract Nat where
  pow := Fract.npow

def Rat.npow (a: ℚ) (n: Nat) : ℚ where
  toFract := a.toFract ^ n
  isReduced := by
    show Fract.isReduced (Fract.npow _ _)
    show (a.num ^ n).natAbs.gcd (a.den ^ n) = _
    rw [Int.natAbs_npow]
    show (‖a.num‖^n).gcd _ = 1
    rw [Nat.pow_gcd_pow, a.isReduced, Nat.one_pow]

instance : Pow ℚ Nat where
  pow := Rat.npow

def Fract.zpow (a: Fract) : Int -> Fract
| .ofNat n => a ^ n
| .negSucc n =>
  if h:a ≈ 0 then
    0
  else
    a.inv h ^ (n + 1)

instance : Pow Fract Int where
  pow := Fract.zpow

def Rat.zpow (a: ℚ) : Int -> ℚ
| .ofNat n => a ^ n
| .negSucc n =>
  if h:a = 0 then
    0
  else
    (a⁻¹?) ^ (n + 1)

instance : Pow ℚ Int where
  pow := Rat.zpow

def Fract.npow.spec (a b: Fract) (n: Nat) : a ≈ b -> a ^ n ≈ b ^ n := by
  intro eq
  replace eq : _ = _ := eq
  show _ = _
  show (a.num ^ n) * ↑(b.den ^ n) = (b.num ^ n) * ↑(a.den ^ n)
  rw [Int.ofNat_npow, Int.ofNat_npow, Int.mul_pow, Int.mul_pow, eq]

def Rat.mk_npow (a: Fract) (n: Nat) : ⟦a⟧ ^ n = ⟦a ^ n⟧ := by
  apply Rat.toFract.inj
  apply Fract.isReduced.spec
  apply Rat.isReduced
  apply Rat.isReduced
  show (Rat.npow _ _).toFract ≈ _
  apply Fract.trans _ (quot.exact' (Q := ℚ)).symm
  unfold Rat.npow
  dsimp
  apply Fract.npow.spec
  exact (quot.exact' (Q := ℚ))

def Rat.mk_zpow (a: Fract) (n: Int) : ⟦a⟧ ^ n = ⟦a ^ n⟧ := by
  cases n
  apply Rat.mk_npow
  show Rat.zpow _ _ = ⟦Fract.zpow _ _⟧
  unfold Rat.zpow Fract.zpow
  dsimp
  split <;> rename_i h
  rw [dif_pos]
  rfl
  exact quot.exact h
  rw [dif_neg (by
    intro g
    apply h
    exact quot.sound g)]
  rw [mk_inv, mk_npow]
  rfl
