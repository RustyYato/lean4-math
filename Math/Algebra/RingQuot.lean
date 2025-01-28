import Math.Algebra.Basic
import Math.Relation.Basic

open Relation

namespace RingQuot

variable [Zero R] [One R] [Add R] [Mul R] [Pow R ℕ] [SMul ℕ R] [NatCast R] [∀n, OfNat R (n + 2)] [IsSemiring R]

variable [Sub R] [Neg R] [SMul ℤ R] [IntCast R] [IsRing R]

variable [Zero S] [One S] [Add S] [Mul S] [Pow S ℕ] [SMul ℕ S] [NatCast S] [∀n, OfNat S (n + 2)] [IsSemiring S]
variable [SMul S R] [AlgebraMap S R] [IsAlgebra S R]

section Rel

inductive Rel (r: R -> R -> Prop): R -> R -> Prop where
| of : r a b -> Rel r a b
| add_left : Rel r a b -> Rel r (a + k) (b + k)
| mul_left : Rel r a b -> Rel r (a * k) (b * k)
| mul_right : Rel r a b -> Rel r (k * a) (k * b)

variable {r: R -> R -> Prop}

def Rel.add_right ⦃a b c : R⦄ (h : Rel r b c) : Rel r (a + b) (a + c) := by
  rw [add_comm a b, add_comm a c]
  exact Rel.add_left h

variable [Sub R] [Neg R] [SMul ℤ R] [IntCast R] [IsRing R]

def Rel.neg ⦃a b : R⦄ (h : Rel r a b) : Rel r (-a) (-b) := by
  rw [neg_eq_neg_one_zsmul, zsmul_eq_intCast_mul,
    neg_eq_neg_one_zsmul b, zsmul_eq_intCast_mul]
  apply Rel.mul_right
  assumption

def Rel.sub_left ⦃a b c : R⦄ (h : Rel r a b) :
    Rel r (a - c) (b - c) := by simp only [sub_eq_add_neg, h.add_left]

def Rel.sub_right ⦃a b c : R⦄ (h : Rel r b c) :
    Rel r (a - b) (a - c) := by simp only [sub_eq_add_neg, h.neg.add_right]

def Rel.smul (k : S) ⦃a b : R⦄ (h : Rel r a b) : Rel r (k • a) (k • b) := by
  rw [smul_def, smul_def]
  apply Rel.mul_right
  assumption

def eqvgen_add : EquivGen (Rel r) a c -> EquivGen (Rel r) b d -> EquivGen (Rel r) (a + b) (c + d)  := by
  intro ac bd
  induction ac generalizing b d with
  | single =>
    apply EquivGen.trans
    apply EquivGen.single
    apply Rel.add_left
    assumption
    rename_i a c ac
    induction bd with
    | single =>
      rename_i b d bd
      apply EquivGen.single
      apply Rel.add_right
      assumption
    | refl => apply EquivGen.refl
    | symm =>
      apply EquivGen.symm
      assumption
    | trans =>
      apply EquivGen.trans <;> assumption
  | refl =>
    rename_i a
    induction bd with
    | single =>
      apply EquivGen.single
      apply Rel.add_right
      assumption
    | refl => apply EquivGen.refl
    | symm =>
      apply EquivGen.symm
      assumption
    | trans =>
      apply EquivGen.trans <;> assumption
  | symm _ ih  =>
    apply EquivGen.symm
    apply ih
    apply EquivGen.symm
    assumption
  | trans _ _ ih₀ ih₁ =>
    apply EquivGen.trans
    apply ih₀
    assumption
    apply ih₁
    apply EquivGen.refl

def eqvgen_mul : EquivGen (Rel r) a c -> EquivGen (Rel r) b d -> EquivGen (Rel r) (a * b) (c * d)  := by
  intro ac bd
  induction ac generalizing b d with
  | single =>
    apply EquivGen.trans
    apply EquivGen.single
    apply Rel.mul_left
    assumption
    rename_i a c ac
    induction bd with
    | single =>
      rename_i b d bd
      apply EquivGen.single
      apply Rel.mul_right
      assumption
    | refl => apply EquivGen.refl
    | symm =>
      apply EquivGen.symm
      assumption
    | trans =>
      apply EquivGen.trans <;> assumption
  | refl =>
    rename_i a
    induction bd with
    | single =>
      apply EquivGen.single
      apply Rel.mul_right
      assumption
    | refl => apply EquivGen.refl
    | symm =>
      apply EquivGen.symm
      assumption
    | trans =>
      apply EquivGen.trans <;> assumption
  | symm _ ih  =>
    apply EquivGen.symm
    apply ih
    apply EquivGen.symm
    assumption
  | trans _ _ ih₀ ih₁ =>
    apply EquivGen.trans
    apply ih₀
    assumption
    apply ih₁
    apply EquivGen.refl

end Rel

def _root_.RingQuot (r: R -> R -> Prop) := Quot (Rel r)

variable {r: R -> R -> Prop}

def mk : R -> RingQuot r := Quot.mk _

scoped notation "⟦" x "⟧" => mk x

private def add : RingQuot r → RingQuot r → RingQuot r := by
  apply Quot.lift
  case f =>
    intro a
    apply Quot.lift
    case f =>
      intro b
      exact ⟦a + b⟧
    case a =>
      intro x y eq
      apply Quot.sound
      apply Rel.add_right
      assumption
  case a =>
    intro a b eq
    ext x
    induction x using Quot.ind
    apply Quot.sound
    apply Rel.add_left
    assumption

private def mul : RingQuot r → RingQuot r → RingQuot r := by
  apply Quot.lift
  case f =>
    intro a
    apply Quot.lift
    case f =>
      intro b
      exact ⟦a * b⟧
    case a =>
      intro x y eq
      apply Quot.sound
      apply Rel.mul_right
      assumption
  case a =>
    intro a b eq
    ext x
    induction x using Quot.ind
    apply Quot.sound
    apply Rel.mul_left
    assumption

private def neg : RingQuot r → RingQuot r := by
  apply Quot.lift
  case f =>
    intro a
    exact ⟦-a⟧
  case a =>
    intro a b eq
    apply Quot.sound
    apply Rel.neg
    assumption

private def sub : RingQuot r → RingQuot r → RingQuot r := by
  apply Quot.lift
  case f =>
    intro a
    apply Quot.lift
    case f =>
      intro b
      exact ⟦a - b⟧
    case a =>
      intro x y eq
      apply Quot.sound
      rw [sub_eq_add_neg, sub_eq_add_neg]
      apply Rel.add_right
      apply Rel.neg
      assumption
  case a =>
    intro a b eq
    ext x
    induction x using Quot.ind
    apply Quot.sound
    rw [sub_eq_add_neg, sub_eq_add_neg]
    apply Rel.add_left
    assumption

private def npow (n: Nat) : RingQuot r -> RingQuot r := by
  apply Quot.lift (⟦· ^ n⟧)
  intro a b eq
  induction n with
  | zero =>
    rw [npow_zero, npow_zero]
  | succ n ih =>
    rw [npow_succ, npow_succ]
    show mul ⟦a ^ n⟧ ⟦a⟧ = mul ⟦b ^ n⟧ ⟦b⟧
    congr 1
    apply Quot.sound
    assumption

private def nsmul (n: Nat) : RingQuot r -> RingQuot r := by
  apply Quot.lift (⟦n • ·⟧)
  intro a b eq
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul]
  | succ n ih =>
    rw [succ_nsmul, succ_nsmul]
    show add ⟦n • a⟧ ⟦a⟧ = add ⟦n • b⟧ ⟦b⟧
    congr 1
    apply Quot.sound
    assumption

private def zsmul (n: Int) : RingQuot r -> RingQuot r := by
  apply Quot.lift (⟦n • ·⟧)
  intro a b eq
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_coe, zsmul_ofNat, zsmul_ofNat]
    show nsmul n ⟦a⟧ = nsmul n ⟦b⟧
    congr 1
    apply Quot.sound
    assumption
  | negSucc n =>
    rw [zsmul_negSucc, zsmul_negSucc]
    show neg (nsmul _ ⟦a⟧) = neg (nsmul _ ⟦b⟧)
    congr 2
    apply Quot.sound
    assumption

private def smul (n: S) : RingQuot r -> RingQuot r := by
  apply Quot.lift (⟦n • ·⟧)
  intro a b r
  apply Quot.sound
  apply Rel.smul
  assumption

instance : NatCast (RingQuot r) := ⟨(⟦·⟧)⟩
instance : IntCast (RingQuot r) := ⟨(⟦·⟧)⟩
instance [OfNat R n] : OfNat (RingQuot r) n := ⟨⟦OfNat.ofNat n⟧⟩

instance instZero : Zero (RingQuot r) := ⟨⟦0⟧⟩
instance instOne : One (RingQuot r) := ⟨⟦1⟧⟩

instance : Add (RingQuot r) := ⟨add⟩
instance : Mul (RingQuot r) := ⟨mul⟩
instance : Neg (RingQuot r) := ⟨neg⟩
instance : Sub (RingQuot r) := ⟨sub⟩
instance : Pow (RingQuot r) ℕ := ⟨flip npow⟩
instance : SMul ℕ (RingQuot r) := ⟨nsmul⟩
instance : SMul ℤ (RingQuot r) := ⟨zsmul⟩
instance : SMul S (RingQuot r) := ⟨smul⟩

@[simp]
def mk_zero : 0 = (⟦0⟧: RingQuot r) := rfl
@[simp]
def mk_one : 1 = (⟦1⟧: RingQuot r) := rfl
@[simp]
def mk_add : (⟦a⟧ + ⟦b⟧: RingQuot r) = ⟦a + b⟧ := rfl
@[simp]
def mk_neg : (-⟦a⟧: RingQuot r) = ⟦-a⟧ := rfl
@[simp]
def mk_sub : (⟦a⟧ - ⟦b⟧: RingQuot r) = ⟦a - b⟧ := rfl
@[simp]
def mk_mul : (⟦a⟧ * ⟦b⟧: RingQuot r) = ⟦a * b⟧ := rfl
@[simp]
def mk_npow {n: Nat} : (⟦a⟧ ^ n: RingQuot r) = ⟦a ^ n⟧ := rfl
@[simp]
def mk_nsmul {n: Nat} : (n • ⟦a⟧: RingQuot r) = ⟦n • a⟧ := rfl
@[simp]
def mk_zsmul {n: Int} : (n • ⟦a⟧: RingQuot r) = ⟦n • a⟧ := rfl
@[simp]
def mk_smul {n: S} : (n • ⟦a⟧: RingQuot r) = ⟦n • a⟧ := rfl

@[cases_eliminator]
def ind {motive: RingQuot r -> Prop} : (mk: ∀a, motive ⟦a⟧) -> ∀a, motive a := Quot.ind
@[cases_eliminator]
def ind₂ {motive: RingQuot r -> RingQuot r -> Prop} : (mk: ∀a b, motive ⟦a⟧ ⟦b⟧) -> ∀a b, motive a b := by
  intro h a b
  cases a; cases b
  apply h
@[cases_eliminator]
def ind₃ {motive: RingQuot r -> RingQuot r -> RingQuot r -> Prop} : (mk: ∀a b c, motive ⟦a⟧ ⟦b⟧ ⟦c⟧) -> ∀a b c, motive a b c := by
  intro h a b c
  cases a, b; cases c
  apply h
@[cases_eliminator]
def ind₄ {motive: RingQuot r -> RingQuot r -> RingQuot r -> RingQuot r -> Prop} : (mk: ∀a b c d, motive ⟦a⟧ ⟦b⟧ ⟦c⟧ ⟦d⟧) -> ∀a b c d, motive a b c d := by
  intro h a b c d
  cases a, b; cases c, d
  apply h

instance : IsAddCommMagma (RingQuot r) where
  add_comm a b := by
    cases a, b
    simp [add_comm]

instance : IsAddMonoid (RingQuot r) where
  add_assoc a b c := by
    cases a, b, c
    simp [add_assoc]
  zero_add a := by
    cases a
    simp [zero_add]
  add_zero a := by
    cases a
    simp [add_zero]
  zero_nsmul a := by
    cases a
    simp [zero_nsmul]
  succ_nsmul n a := by
    cases a
    simp [succ_nsmul]

instance : IsAddGroup (RingQuot r) where
  sub_eq_add_neg a b := by
    cases a, b
    simp [sub_eq_add_neg]
  neg_add_cancel a := by
    cases a
    simp [neg_add_cancel]
  zsmul_ofNat n a := by
    cases a
    simp [zsmul_ofNat]
  zsmul_negSucc n a := by
    cases a
    simp [zsmul_negSucc]

instance [IsCommMagma R] : IsCommMagma (RingQuot r) where
  mul_comm a b := by
    cases a, b
    simp [mul_comm]

instance : IsMonoid (RingQuot r) where
  mul_assoc a b c := by
    cases a, b, c
    simp [mul_assoc]
  one_mul a := by
    cases a
    simp [one_mul]
  mul_one a := by
    cases a
    simp [mul_one]
  npow_zero a := by
    cases a
    simp [npow_zero]
  npow_succ n a := by
    cases a
    simp [npow_succ]

instance instIsSemiring : IsSemiring (RingQuot r) where
  natCast_zero := by
    show ⟦_⟧ = ⟦_⟧
    simp [natCast_zero]
  natCast_succ n := by
    show ⟦_⟧ = ⟦_⟧ + ⟦1⟧
    simp [natCast_succ]
  ofNat_zero := rfl
  ofNat_one := rfl
  ofNat_eq_natCast n := by
    simp [OfNat.ofNat,  NatCast.natCast, ofNat_eq_natCast]
  zero_mul a := by
    cases a
    simp [zero_mul]
  mul_zero a := by
    cases a
    simp [mul_zero]
  left_distrib a b c := by
    cases a, b, c
    simp [mul_add]
  right_distrib a b c := by
    cases a, b, c
    simp [add_mul]
  npow_zero a := by
    cases a
    simp [npow_zero]
  npow_succ n a := by
    cases a
    simp [npow_succ]

instance instIsRing : IsRing (RingQuot r) where
  sub_eq_add_neg := sub_eq_add_neg
  zsmul_ofNat n a := by
    cases a
    simp [zsmul_ofNat]
  zsmul_negSucc n a := by
    cases a
    simp [zsmul_negSucc]
  neg_add_cancel a := by
    cases a
    simp [neg_add_cancel]
  intCast_ofNat n := by
    simp [IntCast.intCast, NatCast.natCast, intCast_ofNat]
  intCast_negSucc := by
    simp [IntCast.intCast, NatCast.natCast, intCast_negSucc]

instance : AlgebraMap S (RingQuot r) where
  toFun s := ⟦algebraMap s⟧
  resp_zero := by
    simp
    rw [resp_zero]
  resp_one := by
    simp
    rw [resp_one]
  resp_add := by
    intro a b
    simp [resp_add]
  resp_mul := by
    intro a b
    simp [resp_mul]

instance instIsAlgebra : IsAlgebra S (RingQuot r) where
  commutes := by
    intro s x
    cases x with| mk x=>
    show ⟦algebraMap _ * _⟧ = ⟦_ * algebraMap _⟧
    congr 1
    apply commutes
  smul_def := by
    intro s x
    cases x
    simp
    congr
    apply smul_def

def mkSemiringHom (r: R -> R -> Prop) : R →+ₙ* RingQuot r where
  toFun := (⟦·⟧)
  resp_zero := rfl
  resp_one := rfl
  resp_mul := rfl
  resp_add := rfl

def mkRingHom (r: R -> R -> Prop) : R →+* RingQuot r where
  toFun := (⟦·⟧)
  resp_zero := rfl
  resp_one := rfl
  resp_mul := rfl
  resp_add := rfl
  resp_neg := rfl

def mkSemiringHom_rel (w: r x y) : mkSemiringHom r x = mkSemiringHom r y := Quot.sound (Rel.of w)
def mkRingHom_rel (w: r x y) : mkRingHom r x = mkRingHom r y := Quot.sound (Rel.of w)

def mkSemiringHom_surj : Function.Surjective (mkSemiringHom r) := by
  intro x
  cases x with | mk x =>
  exists x

def mkRingHom_surj : Function.Surjective (mkRingHom r) := by
  intro x
  cases x with | mk x =>
  exists x

attribute [irreducible] instZero instOne add mul neg sub npow nsmul zsmul mkSemiringHom mkRingHom

end RingQuot
