import Math.Data.Int.Div
import Math.Data.Nat.Gcd
import Math.Data.QuotLike.Basic

section

local instance  : Coe nat int := ⟨int.ofNat⟩

structure Fract where
  num: int
  den: nat
  den_pos: 0 < den

def fract_reduce_den {a: Fract} : (‖a.num‖.gcd a.den: int) ≠ 0 := by
  intro h
  have : ‖a.num‖.gcd a.den = 0 := int.ofNat.inj h
  have ⟨_, h⟩ := nat.of_gcd_eq_zero this
  have := a.den_pos
  rw [h] at this
  contradiction

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply fract_reduce_den)

def Fract.isReduced (a: Fract) : Prop := ‖a.num‖.Coprime a.den
def Fract.reduce (a: Fract) : Fract where
  num := a.num /? ‖a.num‖.gcd a.den
  den := a.den /? ‖a.num‖.gcd a.den
  den_pos := by
    rw [nat.div_of_ge]
    apply nat.zero_lt_succ
    apply nat.dvd.le
    exact a.den_pos
    apply nat.gcd_dvd_right

def Fract.reduce.isReduced (a: Fract) : a.reduce.isReduced := by
  unfold reduce Fract.isReduced
  simp
  rw [int.div_abs, nat.div_den_congr (h := int.abs_ofNat)]
  unfold nat.Coprime
  apply (nat.mul_left_cancel_iff _).mp
  rw [nat.mul_comm, nat.gcd_mul, nat.div_mul_of_dvd, nat.div_mul_of_dvd, nat.mul_one]
  apply nat.gcd_dvd_right
  apply nat.gcd_dvd_left
  invert_tactic

structure Rat extends Fract where
  isReduced: toFract.isReduced

notation "ℚ" => Rat

def Fract.den_nz (a: Fract) : int.ofNat a.den ≠ 0 := by
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
  have p1 : a.num * c.den * b.den = b.num * a.den * c.den := by rw [int.mul_right_comm, ab]
  have p2 : a.num * c.den * b.den = c.num * a.den * b.den := by
    rw [int.mul_right_comm c.num, ←bc, p1]
    ac_rfl
  apply (int.mul_right_cancel_iff _).mp
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
  rw [←int.ofNat_div]
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
