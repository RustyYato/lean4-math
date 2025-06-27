import Math.Algebra.Ring.Defs
import Math.Algebra.Algebra.Hom
import Math.Algebra.Group.Hom

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

variable (R X: Type*) [Zero R] [One R] [Add R] [Mul R]

inductive Rel: Pre R X -> Pre R X -> Prop where
-- ensure that this relation is an equivalence relation
| refl : Rel x x
| symm : Rel x y -> Rel y x
| trans : Rel x y -> Rel y z -> Rel x z

-- ensure that the scalar is a central scalar
| add_scalar {r s: R} : Rel (↑(r + s)) (r + s)
| mul_scalar {r s: R} : Rel (↑(r * s)) (r * s)
| central_scalar {r: R} {x: Pre R X} : Rel (r * x) (x * r)

-- ensure that smul is consistent with addition
| zero_nsmul : Rel (0 • x) 0
| succ_nsmul : Rel ((n + 1) • x) (n • x + x)

-- ensure that npow is consistent with multiplication
| npow_zero : Rel (x ^ 0) 1
| npow_succ : Rel (x ^ (n + 1)) (x ^ n * x)

-- ensure that addition is a commutative monoid
| add_assoc {a b c: Pre R X} : Rel (a + b + c) (a + (b + c))
| add_comm {a b: Pre R X} : Rel (a + b) (b + a)
| add_zero {a: Pre R X} : Rel (a + 0) a

-- ensure that multiplication is a monoid
| mul_assoc {a b c: Pre R X} : Rel (a * b * c) (a * (b * c))
| one_mul {a: Pre R X} : Rel (1 * a) a
| mul_one {a: Pre R X} : Rel (a * 1) a

-- ensure that zero plays well with multiplication
| zero_mul {a: Pre R X} : Rel (0 * a) 0
| mul_zero {a: Pre R X} : Rel (a * 0) 0

-- ensure that multiplication distributes over addition
| mul_add {a b k: Pre R X} : Rel (k * (a + b)) (k * a + k * b)
| add_mul {a b k: Pre R X} : Rel ((a + b) * k) (a * k + b * k)

-- ensure that addition and multiplication play well with the equivalence relation
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

def ofPre [SemiringOps R] : Pre R X -> FreeAlgebra R X := Quotient.mk _

scoped notation "⟦" x "⟧" => ofPre x

@[local induction_eliminator]
def ind [SemiringOps R] {motive: FreeAlgebra R X -> Prop} : (mk: ∀a, motive ⟦a⟧) -> ∀a, motive a := Quotient.ind
@[local induction_eliminator]
def ind₂ [SemiringOps R] {motive: FreeAlgebra R X -> FreeAlgebra R X -> Prop} : (mk: ∀a b, motive ⟦a⟧ ⟦b⟧) -> ∀a b, motive a b := Quotient.ind₂
@[local induction_eliminator]
def ind₃ [SemiringOps R] {motive: FreeAlgebra R X -> FreeAlgebra R X -> FreeAlgebra R X -> Prop} : (mk: ∀a b c, motive ⟦a⟧ ⟦b⟧ ⟦c⟧) -> ∀a b c, motive a b c := by
  intro h a b c
  induction a, b
  induction c
  apply h
@[local induction_eliminator]
def ind₄ [SemiringOps R] {motive: FreeAlgebra R X -> FreeAlgebra R X -> FreeAlgebra R X -> FreeAlgebra R X -> Prop} : (mk: ∀a b c d, motive ⟦a⟧ ⟦b⟧ ⟦c⟧ ⟦d⟧) -> ∀a b c d, motive a b c d := by
  intro h a b c d
  induction a, b
  induction c, d
  apply h

instance [SemiringOps R] : SemiringOps (FreeAlgebra R X) where
  zero := ⟦.scalar 0⟧
  one := ⟦.scalar 1⟧
  natCast n := ⟦.scalar n⟧
  add := by
    apply Quotient.lift₂ (⟦·.add ·⟧)
    intro a b c d ac bd
    apply Quotient.sound
    apply Rel.add_congr
    assumption
    assumption
  mul := by
    apply Quotient.lift₂ (⟦·.mul ·⟧)
    intro a b c d ac bd
    apply Quotient.sound
    apply Rel.mul_congr
    assumption
    assumption
  nsmul n := by
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
  npow := flip <| by
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

private def ofScalar [SemiringOps R] (r: R) : FreeAlgebra R X := ⟦.scalar r⟧

instance [SemiringOps R] : AlgebraMap R (FreeAlgebra R X) where
  toFun := ofScalar
  map_zero := rfl
  map_one := rfl
  map_add := by
    intro x y
    apply Quotient.sound
    apply Rel.add_scalar
  map_mul := by
    intro x y
    apply Quotient.sound
    apply Rel.mul_scalar

instance [SemiringOps R] : SMul R (FreeAlgebra R X) where
  smul x y := algebraMap x * y

instance [RingOps R] : Neg (FreeAlgebra R X) where
  neg x := (-1: R) • x

instance [RingOps R] : RingOps (FreeAlgebra R X) where
  intCast n := ⟦.scalar n⟧
  sub a b := a + -b
  zsmul := zsmulRec

instance [SemiringOps R] : IsAddCommMagma (FreeAlgebra R X) where
  add_comm a b := by
    induction a, b
    apply Quotient.sound
    apply Rel.add_comm

instance [SemiringOps R] : IsAddZeroClass (FreeAlgebra R X) where
  zero_add := by
    intro a; induction a
    rw [add_comm]
    apply Quotient.sound
    apply Rel.add_zero
  add_zero := by
    intro a; induction a
    apply Quotient.sound
    apply Rel.add_zero

instance [SemiringOps R] : IsMulZeroClass (FreeAlgebra R X) where
  zero_mul := by
    intro a; induction a
    apply Quotient.sound
    apply Rel.zero_mul
  mul_zero := by
    intro a; induction a
    apply Quotient.sound
    apply Rel.mul_zero

instance [SemiringOps R] : IsMulOneClass (FreeAlgebra R X) where
  one_mul := by
    intro a; induction a
    apply Quotient.sound
    apply Rel.one_mul
  mul_one := by
    intro a; induction a
    apply Quotient.sound
    apply Rel.mul_one

instance [SemiringOps R] : IsAddSemigroup (FreeAlgebra R X) where
  add_assoc := by
    intro a b c; induction a, b, c
    apply Quotient.sound
    apply Rel.add_assoc

instance [SemiringOps R] : IsSemigroup (FreeAlgebra R X) where
  mul_assoc := by
    intro a b c; induction a, b, c
    apply Quotient.sound
    apply Rel.mul_assoc

instance [SemiringOps R] [IsSemiring R] : IsSemiring (FreeAlgebra R X) where
  natCast_zero := by
    show ⟦_⟧ = ⟦_⟧
    congr
    apply natCast_zero
  natCast_succ := by
    intro n
    show ⟦.scalar _⟧ = ⟦_⟧ + ⟦_⟧
    rw [natCast_succ]
    apply map_add (algebraMap (R := R) (α := FreeAlgebra R X))
  mul_add := by
    intro k a b; induction a, b, k
    apply Quotient.sound
    apply Rel.mul_add
  add_mul := by
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

instance [SemiringOps R] [IsSemiring R] : IsAlgebra R (FreeAlgebra R X) where
  commutes := by
    intro r x
    induction x
    apply Quotient.sound
    apply Rel.central_scalar
  smul_def _ _ := rfl

instance [RingOps R] [IsRing R] : IsAddGroup (FreeAlgebra R X) where
  sub_eq_add_neg _ _ := rfl
  zsmul_ofNat _ _ := rfl
  zsmul_negSucc _ _ := rfl
  neg_add_cancel a := by
    induction a with | mk a =>
    simp [Neg.neg, smul_def]
    conv => { lhs; rhs; rw [←one_mul ⟦a⟧] }
    rw [←add_mul, ←map_one (algebraMap (R := R) (α := FreeAlgebra R X)),
      ←map_add, neg_add_cancel, map_zero, zero_mul]

instance [RingOps R] [IsRing R] : IsAddGroupWithOne (FreeAlgebra R X) where
  natCast_zero := natCast_zero
  natCast_succ := natCast_succ
  intCast_ofNat _ := by
    show ⟦_⟧ = ⟦_⟧
    simp [intCast_ofNat]
  intCast_negSucc n := by
    show ⟦_⟧ = ⟦_⟧
    simp [IntCast.intCast, intCast_negSucc]
    show algebraMap (R := R) (α := FreeAlgebra R X) (-NatCast.natCast (n + 1)) =
        -algebraMap (R := R) (α := FreeAlgebra R X) _
    rw [map_neg]

instance [RingOps R] [IsRing R] : IsRing (FreeAlgebra R X) := IsRing.inst

instance [Zero R] [One R] [Add R] [Mul R] : Inhabited (FreeAlgebra R X) := ⟨Quot.mk _ (.scalar 0)⟩

end FreeAlgebra

namespace FreeAlgebra

open Free.Algebra

def ι (R: Type*) [SemiringOps R] : X → FreeAlgebra R X := fun m ↦ ⟦.of m⟧

def liftFun (R: Type*) {A : Type*}
  [SemiringOps A] [SemiringOps R] [SMul R A] [AlgebraMap R A]
  [IsSemiring A] [IsSemiring R] [IsAlgebra R A] (f : X → A) :
    Pre R X → A
  | .of t => f t
  | .scalar c => algebraMap c
  | .add a b => liftFun R f a + liftFun R f b
  | .mul a b => liftFun R f a * liftFun R f b
  | .nsmul n a => n • liftFun R f a
  | .npow a n => (liftFun R f a) ^ n

@[induction_eliminator, elab_as_elim]
def induction [SemiringOps R] [IsSemiring R] {motive: FreeAlgebra R X -> Prop}
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

def liftAux
  (R: Type*)
  [SemiringOps R] [IsSemiring R] [SemiringOps A] [IsSemiring A]
  [AlgebraMap R A] [SMul R A] [IsAlgebra R A]
  (f: X -> A) : FreeAlgebra R X →ₐ[R] A where
  toFun := by
    apply Quotient.lift (liftFun R f)
    intro a b eq
    induction eq with
    | refl => rfl
    | symm => symm; assumption
    | trans _ _ ih₀ ih₁ => rw [ih₀, ih₁]
    | add_scalar => apply map_add
    | mul_scalar => apply map_mul
    | central_scalar => apply IsAlgebra.commutes
    | zero_nsmul =>
      show 0 • _ = algebraMap _
      rw [zero_nsmul]; symm
      apply map_zero
    | succ_nsmul => apply succ_nsmul
    | npow_zero =>
      show _ ^ 0 = algebraMap _
      rw [npow_zero]; symm
      apply map_one
    | npow_succ => apply npow_succ
    | add_assoc => apply add_assoc
    | add_comm => apply add_comm
    | add_zero =>
      show _ + algebraMap 0 = _
      rw [map_zero, add_zero]
    | mul_assoc => apply mul_assoc
    | one_mul =>
      show algebraMap 1 * _ = _
      rw [map_one, one_mul]
    | mul_one =>
      show _ * algebraMap 1 = _
      rw [map_one, mul_one]
    | zero_mul =>
      show algebraMap 0 * _ = algebraMap 0
      rw [map_zero, zero_mul]
    | mul_zero =>
      show _ * algebraMap 0 = algebraMap 0
      rw [map_zero, mul_zero]
    | mul_add => apply mul_add
    | add_mul => apply add_mul
    | add_congr =>
      show _ + _ = _ + _
      congr
    | mul_congr =>
      show _ * _ = _ * _
      congr

  map_add := by
    intro x y
    induction x, y using ind₂ with | mk x y =>
    rfl
  map_mul := by
    intro x y
    induction x, y using ind₂ with | mk x y =>
    rfl
  map_algebraMap _ := rfl

def lift
  (R: Type*)
  [SemiringOps R] [IsSemiring R] [SemiringOps A] [IsSemiring A]
  [AlgebraMap R A] [SMul R A] [IsAlgebra R A] : (X -> A) ≃ (FreeAlgebra R X →ₐ[R] A) where
  toFun := liftAux R
  invFun f := f ∘ ι R
  leftInv := by
    intro f
    dsimp
    ext x
    rfl
  rightInv := by
    intro f
    dsimp
    apply DFunLike.ext
    intro x
    induction x with
    | grade1 => rfl
    | grade0 => simp [map_algebraMap]
    | add =>
      simp [map_add]
      congr
    | mul =>
      simp [map_mul]
      congr

instance [SemiringOps R] [IsSemiring R] [IsCommMagma R] [Subsingleton X] : IsCommMagma (FreeAlgebra R X) where
  mul_comm a b := by
    induction a generalizing b with
    | grade0 a => rw [commutes]; assumption
    | grade1 a =>
      induction b with
      | grade0 a => rw [commutes]; assumption
      | grade1 b => congr <;> apply Subsingleton.allEq
      | add b₀ b₁ ih₀ ih₁ =>
        rw [mul_add, add_mul, ih₀, ih₁]
      | mul b₀ b₁ ih₀ ih₁ =>
        rw [←mul_assoc, ih₀, mul_assoc, ih₁, mul_assoc]
    | add a₀ a₁ ih₀ ih₁ => rw [add_mul, mul_add, ih₀, ih₁]
    | mul a₀ a₁ ih₀ ih₁  =>
      rw [mul_assoc, ih₁, ←mul_assoc, ih₀, mul_assoc]

end FreeAlgebra

namespace FreeAlgebra

variable {R: Type*} {X: Type*} [SemiringOps R] [IsCommMagma R] [IsSemiring R]
variable {A: Type*}  [SemiringOps A] [IsSemiring A] [IsCommMagma A] [AlgebraMap R A] [SMul R A] [IsAlgebra R A]

@[simp]
def ι_comp_lift (f : X → A) : (lift R f : FreeAlgebra R X → A) ∘ ι R = f := rfl

@[simp]
def lift_ι_apply (f : X → A) (x) : lift R f (ι R x) = f x := rfl

def ι_inj [IsNontrivial R] : Function.Injective (ι R (X := X)) := by
  open scoped Classical in
  intro x y eq
  apply Classical.byContradiction
  intro h
  let f : FreeAlgebra R X →ₐ[R] R := lift _ <| fun z => if x = z then (1: R) else 0
  have h₀ : f (ι R x) = 1 := if_pos rfl
  have h₁ : f (ι R y) = 0 := if_neg h
  rw [eq, h₁] at h₀
  exact zero_ne_one _ h₀

instance [Subsingleton R] : Subsingleton (FreeAlgebra R X) := by
  refine subsingleton_of_trivial ?_
  apply Quotient.sound
  rw [Subsingleton.allEq (α := R) 0 1]

@[simp]
def lift_symm_apply (F : FreeAlgebra R X →ₐ[R] A) : (lift R).symm F = F ∘ ι R := rfl

def hom_ext {f g : FreeAlgebra R X →ₐ[R] A}
    (w : (f : FreeAlgebra R X → A) ∘ ι R = (g : FreeAlgebra R X → A) ∘ ι R) : f = g := by
  rw [← lift_symm_apply, ← lift_symm_apply] at w
  exact (lift R).symm.inj w

/-- The left-inverse of `algebraMap`. -/
def algebraMapInv : FreeAlgebra R X →ₐ[R] R := lift R (fun _ => 0)

def algebraMap.leftInverse : Function.IsLeftInverse algebraMapInv (algebraMap (α := FreeAlgebra R X)) := fun _ => rfl

def algebraMap_inj : Function.Injective (algebraMap (R := R) (α := FreeAlgebra R X)) := algebraMap.leftInverse.Injective

def of_ι_eq_algebraMap [IsNontrivial R] {x: X} {y: R} : ι R x = algebraMap y -> (0: R) = 1 := by
  intro h
  let f₀ : FreeAlgebra R X →ₐ[R] R := lift R (fun _ => 0)
  let f₁ : FreeAlgebra R X →ₐ[R] R := lift R (fun _ => 1)
  have h₀ : f₀ (ι R x) = 0 := rfl
  have h₁ : f₁ (ι R x) = 1 := rfl
  rw [h] at h₀ h₁
  replace h₀: y = 0 := h₀
  replace h₁: y = 1 := h₁
  rwa [h₀] at h₁

def ι_ne_algebraMap [IsNontrivial R] (x: X) (y: R) : ι R x ≠ algebraMap y := by
  intro h; exact zero_ne_one R (of_ι_eq_algebraMap h)

@[simp]
theorem ι_ne_zero [IsNontrivial R] (x : X) : ι R x ≠ 0 :=
  ι_ne_algebraMap x _

@[simp]
theorem ι_ne_one [IsNontrivial R] (x : X) : ι R x ≠ 1 :=
  ι_ne_algebraMap x _

attribute [irreducible] FreeAlgebra lift ι ofScalar

instance [Subsingleton R] : Subsingleton (FreeAlgebra R X) :=
  subsingleton_of_trivial <| by
    rw [←map_zero (algebraMap (R := R)), ←map_one (algebraMap (R := R)),
      Subsingleton.allEq 0 1]

end FreeAlgebra

abbrev FreeRing (α: Type*) : Type _ := FreeAlgebra ℤ α
abbrev FreeSemiring (α: Type*) : Type _ := FreeAlgebra ℕ α

-- a commutative semiring is a free algebra over itself with 0 generators
def FreeAlgebra.self (α: Type*) [SemiringOps α] [IsSemiring α] [IsCommMagma α] : FreeAlgebra α Empty ≃ₐ[α] α := {
  FreeAlgebra.lift α Empty.elim with
  invFun := algebraMap
  leftInv x := by
    simp
    induction x using FreeAlgebra.induction with
    | grade0 r =>
      rw [map_algebraMap]
      rfl
    | grade1 => contradiction
    | add a b iha ihb => rw [map_add, map_add, iha, ihb]
    | mul a b iha ihb => rw [map_mul, map_mul, iha, ihb]
  rightInv x := by
    simp
    rw [map_algebraMap]
    rfl
}

-- the naturals are the free semiring over 0 generators
def FreeSemiring.Nat : FreeSemiring Empty ≃ₐ[ℕ] ℕ := FreeAlgebra.self ℕ

-- the integers are the free ring over 0 generators
def FreeRing.Int : FreeRing Empty ≃ₐ[ℤ] ℤ := FreeAlgebra.self ℤ
