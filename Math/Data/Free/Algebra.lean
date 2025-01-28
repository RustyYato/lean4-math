import Math.Algebra.Ring
import Math.Algebra.Basic
import Math.Relation.RelIso

namespace Free.Algebra

inductive Pre (R A: Type*) where
| of (val: A)
| scalar (val: R)
| mul (a b: Pre R A)
| add (a b: Pre R A)
-- these two are technically unecessary, but it's more efficient
-- to include them so we don't need to rely on nsmulRec or npowRec
| nsmul (n: ℕ) (a: Pre R A)
| npow (a: Pre R A) (n: ℕ)

local instance : Coe R (Algebra.Pre R X) where
  coe := Algebra.Pre.scalar

local instance : Coe X (Algebra.Pre R X) where
  coe := Algebra.Pre.of

local instance : Add (Algebra.Pre R X) := ⟨.add⟩
local instance : Mul (Algebra.Pre R X) := ⟨.mul⟩

local instance : SMul ℕ (Algebra.Pre R X) := ⟨.nsmul⟩
local instance : Pow (Algebra.Pre R X) ℕ := ⟨.npow⟩

local instance [Zero R] : Zero (Algebra.Pre R X) := ⟨.scalar 0⟩
local instance [One R] : One (Algebra.Pre R X) := ⟨.scalar 1⟩

variable (R X: Type*) [Zero R] [One R] [Add R] [Mul R] [Pow R ℕ] [SMul ℕ R] [NatCast R] [∀n, OfNat R (n + 2)]
  [IsCommMagma R] [IsSemiring R]

inductive Rel: Pre R X -> Pre R X -> Prop where
| refl : Rel x x
| symm : Rel x y -> Rel y x
| trans : Rel x y -> Rel y z -> Rel x z

| add_scalar {r s: R} : Rel (↑(r + s)) (r + s)
| mul_scalar {r s: R} : Rel (↑(r * s)) (r * s)
| central_scalar {r: R} {x: Pre R X} : Rel (r * x) (x * r)

| zero_nsmul : Rel (0 • x) 0
| succ_nsmul : Rel ((n + 1) • x) (n • x + x)

| npow_zero : Rel (x ^ 0) 1
| npow_succ : Rel (x ^ (n + 1)) (x ^ n * x)

| add_assoc {a b c: Pre R X} : Rel (a + b + c) (a + (b + c))
| add_comm {a b: Pre R X} : Rel (a + b) (b + a)
| add_zero {a: Pre R X} : Rel (a + 0) a

| mul_assoc {a b c: Pre R X} : Rel (a * b * c) (a * (b * c))
| one_mul {a: Pre R X} : Rel (1 * a) a
| mul_one {a: Pre R X} : Rel (a * 1) a

| zero_mul {a: Pre R X} : Rel (0 * a) 0
| mul_zero {a: Pre R X} : Rel (a * 0) 0

| mul_add {a b k: Pre R X} : Rel (k * (a + b)) (k * a + k * b)
| add_mul {a b k: Pre R X} : Rel ((a + b) * k) (a * k + b * k)

| add_congr {a b c d: Pre R X} : Rel a c -> Rel b d -> Rel (a + b) (c + d)
| mul_congr {a b c d: Pre R X} : Rel a c -> Rel b d -> Rel (a * b) (c * d)

instance : Relation.IsEquiv (Rel R X) where
  refl _ := .refl
  symm := .symm
  trans := .trans

instance setoid : Setoid (Pre R X) := Relation.setoid (Rel R X)

def _root_.FreeAlgebra := Quotient (setoid R X)

attribute [refl] Rel.refl
attribute [symm] Rel.symm

end Free.Algebra

namespace FreeAlgebra

open Free.Algebra Relation

variable {R X: Type*} [Zero R] [One R] [Add R] [Mul R] [Pow R ℕ] [SMul ℕ R] [NatCast R] [∀n, OfNat R (n + 2)]
  [IsCommMagma R] [IsSemiring R]

def ofPre : Pre R X -> FreeAlgebra R X := Quotient.mk _

scoped notation "⟦" x "⟧" => ofPre x

@[local induction_eliminator]
def ind {motive: FreeAlgebra R X -> Prop} : (mk: ∀a, motive ⟦a⟧) -> ∀a, motive a := Quotient.ind
@[local induction_eliminator]
def ind₂ {motive: FreeAlgebra R X -> FreeAlgebra R X -> Prop} : (mk: ∀a b, motive ⟦a⟧ ⟦b⟧) -> ∀a b, motive a b := Quotient.ind₂
@[local induction_eliminator]
def ind₃ {motive: FreeAlgebra R X -> FreeAlgebra R X -> FreeAlgebra R X -> Prop} : (mk: ∀a b c, motive ⟦a⟧ ⟦b⟧ ⟦c⟧) -> ∀a b c, motive a b c := by
  intro h a b c
  induction a, b
  induction c
  apply h
@[local induction_eliminator]
def ind₄ {motive: FreeAlgebra R X -> FreeAlgebra R X -> FreeAlgebra R X -> FreeAlgebra R X -> Prop} : (mk: ∀a b c d, motive ⟦a⟧ ⟦b⟧ ⟦c⟧ ⟦d⟧) -> ∀a b c d, motive a b c d := by
  intro h a b c d
  induction a, b
  induction c, d
  apply h

instance : Add (FreeAlgebra R X) where
  add := by
    apply Quotient.lift₂ (⟦·.add ·⟧)
    intro a b c d ac bd
    apply Quotient.sound
    apply Rel.add_congr
    assumption
    assumption

instance : Mul (FreeAlgebra R X) where
  mul := by
    apply Quotient.lift₂ (⟦·.mul ·⟧)
    intro a b c d ac bd
    apply Quotient.sound
    apply Rel.mul_congr
    assumption
    assumption

instance : SMul ℕ (FreeAlgebra R X) where
  smul n := by
    apply Quotient.lift (⟦.nsmul n ·⟧)
    intro a b ab
    apply Quotient.sound
    induction n with
    | zero =>
      apply Rel.trans
      apply Rel.zero_nsmul
      symm; apply Rel.zero_nsmul
    | succ n ih =>
      apply Rel.trans
      apply Rel.succ_nsmul
      symm
      apply Rel.trans
      apply Rel.succ_nsmul
      symm; apply Rel.add_congr
      assumption
      assumption

instance : Pow (FreeAlgebra R X) ℕ where
  pow := flip <| by
    intro n
    apply Quotient.lift (⟦Pre.npow · n⟧)
    intro a b ab
    apply Quotient.sound
    induction n with
    | zero =>
      apply Rel.trans
      apply Rel.npow_zero
      symm; apply Rel.npow_zero
    | succ n ih =>
      apply Rel.trans
      apply Rel.npow_succ
      symm
      apply Rel.trans
      apply Rel.npow_succ
      symm; apply Rel.mul_congr
      assumption
      assumption

instance : NatCast (FreeAlgebra R X) := ⟨fun n => ⟦.scalar n⟧⟩
instance : OfNat (FreeAlgebra R X) n := ⟨n⟩
instance : Zero (FreeAlgebra R X) := ⟨⟦.scalar 0⟧⟩
instance : One (FreeAlgebra R X) := ⟨⟦.scalar 1⟧⟩

instance : AlgebraMap R (FreeAlgebra R X) where
  toFun := (⟦.scalar ·⟧)
  resp_zero := rfl
  resp_one := rfl
  resp_add := by
    intro x y
    dsimp
    apply Quotient.sound
    apply Rel.add_scalar
  resp_mul := by
    intro x y
    dsimp
    apply Quotient.sound
    apply Rel.mul_scalar

instance : SMul R (FreeAlgebra R X) where
  smul x y := algebraMap x * y

instance : IsAddCommMagma (FreeAlgebra R X) where
  add_comm a b := by
    induction a, b
    apply Quotient.sound
    apply Rel.add_comm

instance : IsAddZeroClass (FreeAlgebra R X) where
  zero_add := by
    intro a; induction a
    rw [add_comm]
    apply Quotient.sound
    apply Rel.add_zero
  add_zero := by
    intro a; induction a
    apply Quotient.sound
    apply Rel.add_zero

instance : IsMulZeroClass (FreeAlgebra R X) where
  zero_mul := by
    intro a; induction a
    apply Quotient.sound
    apply Rel.zero_mul
  mul_zero := by
    intro a; induction a
    apply Quotient.sound
    apply Rel.mul_zero

instance : IsMulOneClass (FreeAlgebra R X) where
  one_mul := by
    intro a; induction a
    apply Quotient.sound
    apply Rel.one_mul
  mul_one := by
    intro a; induction a
    apply Quotient.sound
    apply Rel.mul_one

instance : IsAddSemigroup (FreeAlgebra R X) where
  add_assoc := by
    intro a b c; induction a, b, c
    apply Quotient.sound
    apply Rel.add_assoc

instance : IsSemigroup (FreeAlgebra R X) where
  mul_assoc := by
    intro a b c; induction a, b, c
    apply Quotient.sound
    apply Rel.mul_assoc

instance : IsSemiring (FreeAlgebra R X) where
  natCast_zero := by
    show ⟦_⟧ = ⟦_⟧
    congr
    apply natCast_zero
  natCast_succ := by
    intro n
    show ⟦.scalar (NatCast.natCast _)⟧ = ⟦_⟧ + ⟦_⟧
    rw [natCast_succ]
    apply resp_add (algebraMap (R := R) (A := FreeAlgebra R X))
  ofNat_zero := rfl
  ofNat_one := rfl
  ofNat_eq_natCast _ := rfl
  left_distrib := by
    intro k a b; induction a, b, k
    apply Quotient.sound
    apply Rel.mul_add
  right_distrib := by
    intro k a b; induction a, b, k
    apply Quotient.sound
    apply Rel.add_mul
  zero_nsmul := by
    intro a; induction a
    apply Quotient.sound
    apply Rel.zero_nsmul
  succ_nsmul := by
    intro _ a; induction a
    apply Quotient.sound
    apply Rel.succ_nsmul
  npow_zero := by
    intro a; induction a
    apply Quotient.sound
    apply Rel.npow_zero
  npow_succ := by
    intro n a; induction a
    apply Quotient.sound
    apply Rel.npow_succ

instance : IsAlgebra R (FreeAlgebra R X) where
  commutes := by
    intro r x
    induction x
    apply Quotient.sound
    apply Rel.central_scalar
  smul_def := by
    intro r x
    rfl

instance : Inhabited (FreeAlgebra R X) := ⟨0⟩

def ι (R: Type*) [Zero R] [One R] [Add R] [Mul R] [SMul ℕ R] [Pow R ℕ] [NatCast R] [∀n, OfNat R (n + 2)]
   : X → FreeAlgebra R X := fun m ↦ ⟦.of m⟧

def liftFun {A : Type*}
  [Zero A] [One A] [Add A] [Mul A] [SMul ℕ A] [Pow A ℕ] [NatCast A] [∀n, OfNat A (n + 2)]
  [Zero R] [One R] [Add R] [Mul R] [SMul ℕ R] [Pow R ℕ] [NatCast R] [∀n, OfNat R (n + 2)]
  [SMul R A] [AlgebraMap R A]
  [IsSemiring A] [IsAlgebra R A] (f : X → A) :
    Pre R X → A
  | .of t => f t
  | .scalar c => algebraMap c
  | .add a b => liftFun f a + liftFun f b
  | .mul a b => liftFun f a * liftFun f b
  | .nsmul n a => n • liftFun f a
  | .npow a n => (liftFun f a) ^ n

end FreeAlgebra

namespace FreeAlgebra

open Free.Algebra

variable {R X: Type*} [Zero R] [One R] [Add R] [Mul R] [Pow R ℕ] [SMul ℕ R] [NatCast R] [∀n, OfNat R (n + 2)]
  [IsCommMagma R] [IsSemiring R]

@[elab_as_elim, induction_eliminator]
def induction {motive: FreeAlgebra R X -> Prop}
  (grade0: ∀r: R, motive (algebraMap r))
  (grade1: ∀x, motive (ι R x))
  (add: ∀a b, motive a -> motive b -> motive (a + b))
  (mul: ∀a b, motive a -> motive b -> motive (a * b)):
  ∀x, motive x := by
  intro x
  induction x using ind with | mk x =>
  induction x with
  | scalar x => apply grade0
  | of x => apply grade1
  | mul a b =>
    show motive (⟦a⟧ * ⟦b⟧)
    apply mul
    assumption
    assumption
  | add a b =>
    show motive (⟦a⟧ + ⟦b⟧)
    apply add
    assumption
    assumption
  | nsmul n a =>
    show motive (n • ⟦a⟧)
    induction n with
    | zero =>
      rw [zero_nsmul]
      apply grade0
    | succ n ih =>
      rw [succ_nsmul]
      apply add
      assumption
      assumption
  | npow a n =>
    show motive (⟦a⟧ ^ n)
    induction n with
    | zero =>
      rw [npow_zero]
      apply grade0
    | succ n ih =>
      rw [npow_succ]
      apply mul
      assumption
      assumption

attribute [irreducible] ι

end FreeAlgebra
