import Math.Data.Nat.Gcd
import Math.Data.Int.Basic
import Math.Ops.Checked
import Math.Algebra.Norm.Basic
import Math.Logic.Nontrivial
import Math.Relation.Basic
import Math.Algebra.Field.Basic
import Math.Algebra.Semiring.Char
import Math.Algebra.Ring.Basic

namespace Rat

@[ext]
structure Fract where
  num: Int
  den: Nat
  den_pos: 0 < den := by exact Nat.zero_lt_succ _
deriving Repr, DecidableEq

def Fract.den_nz (f: Fract) : f.den ≠ 0 := by
  exact Nat.ne_of_lt' f.den_pos

def Fract.den_nz' (a: Fract) : Int.ofNat a.den ≠ 0 := by
  cases a  with | mk a d p =>
  dsimp
  intro h
  cases h
  contradiction

private def fract_reduce_den {a: Fract} : (‖a.num‖.gcd a.den: Int) ≠ 0 := by
  intro h
  have : ‖a.num‖.gcd a.den = 0 := Int.ofNat.inj h
  have h := Nat.eq_zero_of_gcd_eq_zero_right this
  have := Int.ofNat_lt.mpr a.den_pos
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
    have h : a.den = 0 := Nat.eq_zero_of_gcd_eq_zero_right h
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
    rw [←Int.natAbs_ofNat (‖a.num‖.gcd a.den)]
  }
  show (Int.natAbs _ * _).gcd _ = _
  rw [←Int.natAbs_mul, Int.ediv_mul_cancel, Nat.div_mul_cancel, Nat.one_mul]
  rfl
  apply Nat.gcd_dvd_right
  apply Int.dvd_natAbs.mp
  apply Int.ofNat_dvd.mpr
  apply Nat.gcd_dvd_left

def Fract.Equiv (a b: Fract) : Prop := a.num * b.den = b.num * a.den

@[refl]
def Fract.Equiv.refl (a: Fract) : a.Equiv a := rfl
@[symm]
def Fract.Equiv.symm {a b: Fract} : a.Equiv b -> b.Equiv a := Eq.symm
def Fract.Equiv.trans {a b c: Fract} : a.Equiv b -> b.Equiv c -> a.Equiv c := by
  unfold Equiv
  intro ab bc
  have p1 : a.num * c.den * b.den = b.num * a.den * c.den := by rw [Int.mul_right_comm, ab]
  have p2 : a.num * c.den * b.den = c.num * a.den * b.den := by
    rw [Int.mul_right_comm c.num, ←bc, p1]
    ac_rfl
  apply (Int.mul_eq_mul_right_iff _).mp
  assumption
  exact b.den_nz'

instance : Relation.IsRefl Fract.Equiv := ⟨Fract.Equiv.refl⟩
instance : Relation.IsSymmetric Fract.Equiv := ⟨Fract.Equiv.symm⟩
instance : Relation.IsTrans Fract.Equiv := ⟨Fract.Equiv.trans⟩
instance : Setoid Fract := Relation.setoid Fract.Equiv

def Fract.isReduced.spec (a b: Fract) : a.isReduced -> b.isReduced -> a ≈ b -> a = b := by
  intro ared bred h
  replace h : _ * _  = _ * _ := h
  cases a with | mk an ad adpos =>
  cases b with | mk bn bd bdpos =>
  unfold isReduced at ared bred
  simp at *
  have sign_eq : (an * bd).sign = (bn * ad).sign := by rw [h]
  rw [Int.sign_mul, Int.sign_mul, Int.sign_ofNat_of_nonzero (Nat.ne_zero_of_lt adpos)
    , Int.sign_ofNat_of_nonzero (Nat.ne_zero_of_lt bdpos), Int.mul_one, Int.mul_one] at sign_eq
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

def Fract.reduce.spec (a: Fract) : a ≈ a.reduce := by
  cases a with | mk n d dpos =>
  show _ * _ = _ * _
  unfold reduce
  dsimp only [Int.ofNat_ediv]
  rw [←Int.mul_ediv_assoc, Int.mul_comm n, Int.mul_ediv_assoc, Int.mul_comm]
  apply Int.dvd_natAbs.mp
  apply Int.ofNat_dvd.mpr
  apply Nat.gcd_dvd_left
  apply Int.dvd_natAbs.mp
  apply Int.ofNat_dvd.mpr
  apply Nat.gcd_dvd_right

def _root_.Rat := Quotient (Relation.setoid Fract.Equiv)
notation "ℚ" => Rat

def mk : Fract -> ℚ := Quotient.mk _

scoped notation "⟦" x "⟧" => mk x

@[cases_eliminator]
def ind {motive: ℚ -> Prop} : (mk: ∀a, motive ⟦a⟧) -> ∀a, motive a := Quotient.ind
@[cases_eliminator]
def ind₂ {motive: ℚ -> ℚ -> Prop} : (mk: ∀a b, motive ⟦a⟧ ⟦b⟧) -> ∀a b, motive a b := Quotient.ind₂
@[cases_eliminator]
def ind₃ {motive: ℚ -> ℚ -> ℚ -> Prop} : (mk: ∀a b c, motive ⟦a⟧ ⟦b⟧ ⟦c⟧) -> ∀a b c, motive a b c := by
  intro h a b c
  cases a, b; cases c
  apply h
@[cases_eliminator]
def ind₄ {motive: ℚ -> ℚ -> ℚ -> ℚ -> Prop} : (mk: ∀a b c d, motive ⟦a⟧ ⟦b⟧ ⟦c⟧ ⟦d⟧) -> ∀a b c d, motive a b c d := by
  intro h a b c d
  cases a, b; cases c, d
  apply h
def sound {a b: Fract} :  a ≈ b -> ⟦a⟧ = ⟦b⟧ := Quotient.sound
def exact {a b: Fract} :  ⟦a⟧ = ⟦b⟧ -> a ≈ b := Quotient.exact
def exact_ne {a b: Fract} :  ⟦a⟧ ≠ ⟦b⟧ -> ¬a ≈ b := fun g h => g (sound h)

instance : @DecidableRel Fract Fract (· ≈ ·) := inferInstanceAs (∀_ _, Decidable (_ = _))
instance : DecidableEq ℚ := inferInstanceAs (DecidableEq (Quotient (Relation.setoid Fract.Equiv)))

def toFract : ℚ -> Fract := by
  apply Quotient.lift Fract.reduce
  intro a b eq
  apply Fract.isReduced.spec
  apply Fract.reduce.isReduced
  apply Fract.reduce.isReduced
  apply Relation.IsTrans.trans
  apply (Fract.reduce.spec _).symm
  apply Relation.IsTrans.trans eq
  apply Fract.reduce.spec

def toFract.inj : ∀{a b: ℚ}, a.toFract = b.toFract ↔ a = b :=
  Function.Injective.eq_iff <| by
    intro a b eq
    cases a, b with | mk a b =>
    replace eq: a.reduce = b.reduce := eq
    apply sound
    apply (Fract.reduce.spec _).trans
    rw [eq]
    apply (Fract.reduce.spec _).symm

def Fract.ofNat (n: Nat) : Fract where
  num := n
  den := 1

def Fract.ofInt (n: Int) : Fract where
  num := n
  den := 1

def Rat.ofNat (n: Nat) : ℚ := ⟦.ofNat n⟧
def Rat.ofInt (n: Int) : ℚ := ⟦.ofInt n⟧

attribute [coe] Fract.ofNat Fract.ofInt Rat.ofNat Rat.ofInt

instance : NatCast Fract := ⟨Fract.ofNat⟩
instance : IntCast Fract := ⟨Fract.ofInt⟩

instance : NatCast ℚ := ⟨Rat.ofNat⟩
instance : IntCast ℚ := ⟨Rat.ofInt⟩

instance : OfNat Fract n := ⟨n⟩
instance : OfNat ℚ n := ⟨n⟩

instance : IsNontrivial ℚ where
  exists_ne := ⟨0, 1, by decide⟩

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

instance : Add ℚ where
  add := by
    apply Quotient.lift₂ (⟦· + ·⟧)
    intros
    apply sound
    apply Fract.add.spec <;> assumption

@[simp]
def mk_add (a b: Fract) : ⟦a⟧ + ⟦b⟧ = ⟦a + b⟧ := rfl

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

instance : Mul ℚ where
  mul := by
    apply Quotient.lift₂ (⟦· * ·⟧)
    intros
    apply sound
    apply Fract.mul.spec <;> assumption

@[simp]
def mk_mul (a b: Fract) : ⟦a⟧ * ⟦b⟧ = ⟦a * b⟧ := rfl

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
  simp [←neg_mul_left]
  rw [ab]

instance : Neg ℚ where
  neg := by
    apply Quotient.lift (⟦-·⟧)
    intro a b eq
    apply sound
    apply Fract.neg.spec
    assumption

@[simp]
def mk_neg (a: Fract) : -⟦a⟧ = ⟦-a⟧ := rfl

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
  simp [←neg_mul_left]
  rw [Int.sub_eq_add_neg]

instance : Sub ℚ where
  sub := by
    apply Quotient.lift₂ (⟦· - ·⟧)
    intros _ _ _ _ ac bd
    rw [Fract.sub_eq_add_neg, Fract.sub_eq_add_neg]
    simp only [←mk_neg, ←mk_add]
    rw [sound ac, sound bd]

@[simp]
def mk_sub (a b: Fract) : ⟦a⟧ - ⟦b⟧ = ⟦a - b⟧ := rfl

def Fract.inv (a: Fract) (h: ¬a ≈ 0) : Fract where
  num := a.num.sign * a.den
  den := ‖a.num‖
  den_pos := by
    apply Nat.zero_lt_of_ne_zero
    intro g
    apply h
    show _ = _
    erw [Int.zero_mul, Int.mul_one]
    exact Int.natAbs_eq_zero.mp g

instance : CheckedInvert Fract (fun a => ¬a ≈ 0) where
  checked_invert := Fract.inv

def Fract.inv.spec (a b: Fract) (h₀: ¬a ≈ 0) (h₁: ¬b ≈ 0) : a ≈ b -> a⁻¹? ≈ b⁻¹? := by
  intro eq
  replace eq : _ * _ = _ * _ := eq
  show _ * _ = _ * _
  simp [CheckedInvert.checked_invert, Fract.inv, Norm.norm]
  suffices a.num.sign = b.num.sign by
    rw [this, Int.mul_comm b.num.sign, Int.mul_assoc, Int.sign_mul_natAbs b.num]
    rw [←this, Int.mul_comm a.num.sign, Int.mul_assoc, Int.sign_mul_natAbs a.num]
    rw [Int.mul_comm, ←eq, Int.mul_comm]
  have : (a.num * b.den).sign = (b.num * a.den).sign := by rw [eq]
  rw [Int.sign_mul, Int.sign_mul, Int.sign_ofNat_of_nonzero a.den_nz,
    Int.sign_ofNat_of_nonzero b.den_nz, Int.mul_one, Int.mul_one] at this
  assumption

instance : CheckedInv? ℚ where
  checked_invert a := by
    apply a.hrecOn (motive := fun a: ℚ => a ≠ 0 -> ℚ) (fun a h => ⟦Fract.inv a (exact_ne h)⟧)
    intro a b h
    apply Function.hfunext
    rw [Quotient.sound h]
    intro ha hb eq
    apply heq_of_eq
    apply Quotient.sound
    apply Fract.inv.spec
    assumption

def ne_zero_of_not_equiv_zero (a: Fract) : ¬a ≈ 0 -> ⟦a⟧ ≠ 0 := fun h g => h (exact g)

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply ne_zero_of_not_equiv_zero; assumption)

def not_equiv_zero_of_ne_zero (a: Fract) : ⟦a⟧ ≠ 0 -> ¬a ≈ 0 := exact_ne

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply not_equiv_zero_of_ne_zero; invert_tactic)

def mk_inv (a: Fract) (h: ¬a ≈ 0) : ⟦a⟧⁻¹? = ⟦a⁻¹?⟧ := rfl

instance : CheckedDiv? ℚ where
  checked_div a b h := a * b⁻¹?

def Fract.npow (a: Fract) (n: Nat) : Fract where
  num := a.num ^ n
  den := a.den ^ n
  den_pos := Nat.pow_pos a.den_pos

instance : Pow Fract ℕ := ⟨.npow⟩

@[simp]
def Fract.npow_num (a: Fract) (n: Nat) : (a ^ n).num = a.num ^ n := rfl
@[simp]
def Fract.npow_den (a: Fract) (n: Nat) : (a ^ n).den = a.den ^ n := rfl

def Fract.npow.spec (a b: Fract) (n: Nat) : a ≈ b -> a ^ n ≈ b ^ n := by
  intro eq
  show _ = _
  simp
  rw [Int.pow_ofNat, Int.pow_ofNat, Int.mul_pow, Int.mul_pow, eq]

instance : SMul ℕ ℚ where
  smul n a := n * a
instance : SMul ℤ ℚ where
  smul n a := n * a
instance : Pow ℚ ℕ where
  pow := by
    apply Quotient.lift (⟦· ^ ·⟧)
    intro a b eq
    ext n
    apply Quotient.sound
    apply Fract.npow.spec
    assumption
instance : CheckedIntPow? ℚ := instCheckedIntPow

@[local simp] def smul_eq (n: ℕ) (a: ℚ) : n • a = n * a := rfl
@[local simp] def zmul_eq (n: ℤ) (a: ℚ) : n • a = n * a := rfl

@[simp] def Fract.natCast_num (n: Nat) : Fract.num n = n := rfl
@[simp] def Fract.intCast_num (n: Int) : Fract.num n = n := rfl
@[simp] def Fract.natCast_den (n: Nat) : Fract.den n = 1 := rfl
@[simp] def Fract.intCast_den (n: Int) : Fract.den n = 1 := rfl

@[simp] def Fract.ofNat_num (n: Nat) : Fract.num (Fract.ofNat n) = n := rfl
@[simp] def Fract.ofInt_num (n: Int) : Fract.num (Fract.ofInt n) = n := rfl
@[simp] def Fract.ofNat_den (n: Nat) : Fract.den (Fract.ofNat n) = 1 := rfl
@[simp] def Fract.ofInt_den (n: Int) : Fract.den (Fract.ofInt n) = 1 := rfl

instance : IsField ℚ where
  zero_add a := by
    cases a with | mk a =>
    apply sound
    show _ = _
    simp
  add_zero a := by
    cases a with | mk a =>
    apply sound
    show _ = _
    simp
  zero_mul a := by
    cases a with | mk a =>
    apply sound
    show _ = _
    simp
  mul_zero a := by
    cases a with | mk a =>
    apply sound
    show _ = _
    simp
  one_mul a := by
    cases a with | mk a =>
    apply sound
    show _ = _
    simp
  mul_one a := by
    cases a with | mk a =>
    apply sound
    show _ = _
    simp
  add_comm a b := by
    cases a, b with | mk a b =>
    apply sound
    show _ = _
    simp [Int.add_comm, Int.mul_comm]
  add_assoc a b c := by
    cases a, b, c with | mk a b c =>
    apply sound
    show _ = _
    simp [Int.mul_add, Int.add_mul]
    ac_rfl
  mul_comm a b := by
    cases a, b with | mk a b =>
    apply sound
    show _ = _
    simp [Int.mul_comm]
  mul_assoc a b c := by
    cases a, b, c with | mk a b c =>
    apply sound
    show _ = _
    simp [Int.mul_assoc]
  natCast_zero := rfl
  natCast_succ n := by
    apply sound
    show _ = _
    simp
  left_distrib k a b := by
    cases k, a, b
    apply sound
    show _ = _
    simp [Int.add_mul, Int.mul_add]
    ac_rfl
  right_distrib a b k := by
    cases k, a, b
    apply sound
    show _ = _
    simp [Int.add_mul, Int.mul_add]
    ac_rfl
  sub_eq_add_neg a b := by
    cases a, b
    apply sound
    show _ = _
    simp [Int.sub_eq_add_neg, ←neg_mul_left]
  zsmul_ofNat n a := by
    cases a
    apply sound
    show _ = _
    simp
  zsmul_negSucc n a := by
    cases a
    apply sound
    show _ = _
    simp [Fract.ofInt, ←Int.neg_mul]
    rfl
  neg_add_cancel a := by
    cases a
    apply sound
    show _ = _
    simp [Int.add_left_neg, ←neg_mul_left]
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl
  mul_inv?_cancel a h := by
    cases a
    apply sound
    show _ = _
    simp [Fract.inv]
    rw [←Int.mul_assoc, Int.mul_sign_self, Int.mul_comm]
    rfl
  zero_nsmul a := by
    cases a
    apply sound
    show _ = _
    simp
  succ_nsmul n a := by
    cases a
    apply sound
    show _ = _
    simp [Int.add_mul]
    ac_rfl
  npow_zero a := by
    cases a
    apply sound
    show _ = _
    simp [Int.pow_zero]
  npow_succ n a := by
    cases a
    apply sound
    show _ = _
    simp [Int.pow_succ, Nat.pow_succ]
  div?_eq_mul_inv? _ _ _ := rfl
  zpow?_ofNat _ _ := rfl
  zpow?_negSucc _ _ _ := rfl

instance : IsNonCommField ℚ := (inferInstanceAs (IsField ℚ)).toIsNonCommField
instance : IsRing ℚ := (inferInstanceAs (IsField ℚ)).toIsRing
instance : IsSemiring ℚ := (inferInstanceAs (IsField ℚ)).toIsSemiring

def ofIntHom : ℤ ↪+* ℚ where
  toFun := algebraMap
  map_zero := map_zero _
  map_one := map_one _
  map_add := map_add _
  map_mul := map_mul _
  inj' := by
    intro x y eq
    have : _ = _ := Quotient.exact eq
    erw [mul_one, mul_one] at this
    assumption

instance : HasChar ℚ 0 := HasChar.of_ring_emb ofIntHom

def add_half (a: ℚ) : a = a /? 2 + a /? 2 := by
  rw [←two_mul, div?_eq_mul_inv?, mul_comm, mul_assoc, inv?_mul_cancel, mul_one]
def sub_half (a: ℚ) : a - a /? 2 = a /? 2 := by
  conv => { lhs; lhs ; rw [add_half a] }
  rw [add_sub_assoc, add_sub_cancel]

def mul_nonzero (a b: ℚ) : a ≠ 0 -> b ≠ 0 -> a * b ≠ 0 := by
  intro ha hb h
  cases of_mul_eq_zero h <;> contradiction

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply mul_nonzero <;> assumption)

def neg_nonzero (a: ℚ) : a ≠ 0 -> -a ≠ 0 := by
  intro ha
  rw [neg_eq_neg_one_zsmul]
  apply mul_nonzero
  decide
  assumption

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply neg_nonzero <;> assumption)

def natCast_nonzero (n: Nat) : ((n + 1: ℕ): ℚ) ≠ 0 := by
  intro ha
  have eq : _ = _ := Quotient.exact ha
  simp at eq
  have : (n: Int) + 1 = (n + 1: Nat) := Int.ofNat_add _ _
  rw [this] at eq
  nomatch eq

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply natCast_nonzero)

instance (q: ℚ) : Decidable (NeZero q) :=
  if h:q = 0 then
    .isFalse fun g => g.out h
  else
    .isTrue ⟨h⟩

instance : NeZero (2: ℚ) := by decide

def binarySearch (P: ℚ -> Bool) (a b: ℚ) : ℕ -> ℚ
| 0 => a
| n + 1 =>
  if P (midpoint a b) then
    binarySearch P a (midpoint a b) n
  else
    binarySearch P (midpoint a b) b n

end Rat
