-- import Math.Data.Int.Div
-- import Math.Data.Nat.Gcd
import Math.Data.StdInt.AbsoluteValue
import Math.Data.QuotLike.Basic

section

structure Fract where
  num: Int
  den: Nat
  den_pos: 0 < den

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
  rw [←Int.ofNat_ediv]
  sorry

def Fract.isReduced.spec (a b: Fract) : a.isReduced -> b.isReduced -> a ≈ b -> a = b := by
  intro ared bred h
  sorry

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

end
