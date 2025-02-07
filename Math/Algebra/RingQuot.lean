import Math.Algebra.Hom
import Math.Relation.Basic

open Relation

namespace RingQuot

section Rel

section

variable [SemiringOps S] [SemiringOps R] [SMul S R] [IsSemiring R]

variable [AlgebraMap S R] [IsAlgebra S R]

inductive Rel (r: R -> R -> Prop): R -> R -> Prop where
| of : r a b -> Rel r a b
| add_left : Rel r a b -> Rel r (a + k) (b + k)
| mul_left : Rel r a b -> Rel r (a * k) (b * k)
| mul_right : Rel r a b -> Rel r (k * a) (k * b)

variable {r: R -> R -> Prop}

def Rel.add_right ⦃a b c : R⦄ (h : Rel r b c) : Rel r (a + b) (a + c) := by
  rw [add_comm a b, add_comm a c]
  exact Rel.add_left h

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

end

variable [RingOps S] [RingOps R] [SMul S R] [IsRing R]

variable [AlgebraMap S R] [IsAlgebra S R]

def Rel.neg ⦃a b : R⦄ (h : Rel r a b) : Rel r (-a) (-b) := by
  rw [neg_eq_neg_one_zsmul, zsmul_eq_intCast_mul,
    neg_eq_neg_one_zsmul b, zsmul_eq_intCast_mul]
  apply Rel.mul_right
  assumption

def Rel.sub_left ⦃a b c : R⦄ (h : Rel r a b) : Rel r (a - c) (b - c) := by
      rw [sub_eq_add_neg]
      simp only [sub_eq_add_neg, h.add_left]

def Rel.sub_right ⦃a b c : R⦄ (h : Rel r b c) :
    Rel r (a - b) (a - c) := by simp only [sub_eq_add_neg, h.neg.add_right]

end Rel

def _root_.RingQuot [SemiringOps R] (r: R -> R -> Prop) := Quot (Rel r)

variable {r: R -> R -> Prop}

def mk [SemiringOps R] : R -> RingQuot r := Quot.mk _

scoped notation "⟦" x "⟧" => mk x

private def add [SemiringOps R] [IsSemiring R] : RingQuot r → RingQuot r → RingQuot r := by
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

private def mul [SemiringOps R] : RingQuot r → RingQuot r → RingQuot r := by
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

private def neg [RingOps R] [IsRing R] : RingQuot r → RingQuot r := by
  apply Quot.lift
  case f =>
    intro a
    exact ⟦-a⟧
  case a =>
    intro a b eq
    apply Quot.sound
    apply Rel.neg
    assumption

private def sub [RingOps R] [IsRing R] : RingQuot r → RingQuot r → RingQuot r := by
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

private def npow [SemiringOps R] [IsSemiring R] (n: Nat) : RingQuot r -> RingQuot r := by
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

private def nsmul [SemiringOps R] [IsSemiring R] (n: Nat) : RingQuot r -> RingQuot r := by
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

private def zsmul [RingOps R] [IsRing R] (n: Int) : RingQuot r -> RingQuot r := by
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

private def smul [SemiringOps R] [SemiringOps S] [IsSemiring R] [SMul S R] [AlgebraMap S R] [IsAlgebra S R] (n: S) : RingQuot r -> RingQuot r := by
  apply Quot.lift (⟦n • ·⟧)
  intro a b r
  apply Quot.sound
  apply Rel.smul
  assumption

instance [SemiringOps R] : NatCast (RingQuot r) := ⟨(⟦·⟧)⟩
instance [RingOps R] : IntCast (RingQuot r) := ⟨(⟦·⟧)⟩
instance [SemiringOps R] [OfNat R n] : OfNat (RingQuot r) n := ⟨⟦OfNat.ofNat n⟧⟩

instance instZero [SemiringOps R] : Zero (RingQuot r) := ⟨⟦0⟧⟩
instance instOne [SemiringOps R] : One (RingQuot r) := ⟨⟦1⟧⟩

instance [SemiringOps R] [IsSemiring R] : Add (RingQuot r) := ⟨add⟩
instance [SemiringOps R] : Mul (RingQuot r) := ⟨mul⟩
instance [RingOps R] [IsRing R] : Neg (RingQuot r) := ⟨neg⟩
instance [RingOps R] [IsRing R] : Sub (RingQuot r) := ⟨sub⟩
instance [SemiringOps R] [IsSemiring R] : Pow (RingQuot r) ℕ := ⟨flip npow⟩
instance [SemiringOps R] [IsSemiring R] : SMul ℕ (RingQuot r) := ⟨nsmul⟩
instance [RingOps R] [IsRing R] : SMul ℤ (RingQuot r) := ⟨zsmul⟩
instance [SemiringOps R] [SemiringOps S] [IsSemiring R] [SMul S R] [AlgebraMap S R] [IsAlgebra S R] : SMul S (RingQuot r) := ⟨smul⟩

instance instSemiringOps [SemiringOps R] [IsSemiring R] : SemiringOps (RingQuot r) where
instance instRingOps [RingOps R] [IsRing R] : RingOps (RingQuot r) where

@[simp]
def mk_zero [SemiringOps R] : 0 = (⟦0⟧: RingQuot r) := rfl
@[simp]
def mk_one [SemiringOps R] : 1 = (⟦1⟧: RingQuot r) := rfl
@[simp]
def mk_add [SemiringOps R] [IsSemiring R] : (⟦a⟧ + ⟦b⟧: RingQuot r) = ⟦a + b⟧ := rfl
@[simp]
def mk_neg [RingOps R] [IsRing R] : (-⟦a⟧: RingQuot r) = ⟦-a⟧ := rfl
@[simp]
def mk_sub [RingOps R] [IsRing R] : (⟦a⟧ - ⟦b⟧: RingQuot r) = ⟦a - b⟧ := rfl
@[simp]
def mk_mul [SemiringOps R] : (⟦a⟧ * ⟦b⟧: RingQuot r) = ⟦a * b⟧ := rfl
@[simp]
def mk_npow [SemiringOps R] [IsSemiring R] {n: Nat} : (⟦a⟧ ^ n: RingQuot r) = ⟦a ^ n⟧ := rfl
@[simp]
def mk_nsmul [SemiringOps R] [IsSemiring R] {n: Nat} : (n • ⟦a⟧: RingQuot r) = ⟦n • a⟧ := rfl
@[simp]
def mk_zsmul [RingOps R] [IsRing R] {n: Int} : (n • ⟦a⟧: RingQuot r) = ⟦n • a⟧ := rfl
@[simp]
def mk_smul [SemiringOps R] [SemiringOps S] [IsSemiring R] [SMul S R] [AlgebraMap S R] [IsAlgebra S R] {n: S} : (n • ⟦a⟧: RingQuot r) = ⟦n • a⟧ := rfl

@[cases_eliminator]
def ind [SemiringOps R] {motive: RingQuot r -> Prop} : (mk: ∀a, motive ⟦a⟧) -> ∀a, motive a := Quot.ind
@[cases_eliminator]
def ind₂ [SemiringOps R] {motive: RingQuot r -> RingQuot r -> Prop} : (mk: ∀a b, motive ⟦a⟧ ⟦b⟧) -> ∀a b, motive a b := by
  intro h a b
  cases a; cases b
  apply h
@[cases_eliminator]
def ind₃ [SemiringOps R] {motive: RingQuot r -> RingQuot r -> RingQuot r -> Prop} : (mk: ∀a b c, motive ⟦a⟧ ⟦b⟧ ⟦c⟧) -> ∀a b c, motive a b c := by
  intro h a b c
  cases a, b; cases c
  apply h
@[cases_eliminator]
def ind₄ [SemiringOps R] {motive: RingQuot r -> RingQuot r -> RingQuot r -> RingQuot r -> Prop} : (mk: ∀a b c d, motive ⟦a⟧ ⟦b⟧ ⟦c⟧ ⟦d⟧) -> ∀a b c d, motive a b c d := by
  intro h a b c d
  cases a, b; cases c, d
  apply h

instance [SemiringOps R] [IsSemiring R] : IsAddCommMagma (RingQuot r) where
  add_comm a b := by
    cases a, b
    simp [add_comm]

instance [SemiringOps R] [IsSemiring R] : SemiringOps (RingQuot r) where
instance [RingOps R] [IsRing R] : RingOps (RingQuot r) where

instance [SemiringOps R] [IsSemiring R] [IsCommMagma R] : IsCommMagma (RingQuot r) where
  mul_comm a b := by
    cases a, b
    simp [mul_comm]

instance instIsSemiring [SemiringOps R] [IsSemiring R] : IsSemiring (RingQuot r) where
  add_assoc a b c := by
    cases a, b, c
    simp [add_assoc]
  zero_add a := by
    cases a
    simp [zero_add]
  add_zero a := by
    cases a
    simp [add_zero]
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
  zero_nsmul a := by
    cases a
    simp [zero_nsmul]
  succ_nsmul n a := by
    cases a
    simp [succ_nsmul]
  natCast_zero := by
    show ⟦_⟧ = ⟦_⟧
    simp [natCast_zero]
  natCast_succ n := by
    show ⟦_⟧ = ⟦_⟧ + ⟦1⟧
    simp [natCast_succ]
  ofNat_eq_natCast n := by
    show ⟦_⟧ = ⟦_⟧
    simp [ofNat_eq_natCast]
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

instance instIsRing [RingOps R] [IsRing R] : IsRing (RingQuot r) where
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
  intCast_ofNat n := by
    show ⟦_⟧ = ⟦_⟧
    rw [intCast_ofNat]
  intCast_negSucc _ := by
    show ⟦_⟧ = -⟦_⟧
    simp [intCast_negSucc]

instance [SemiringOps R] [SemiringOps S] [SMul S R] [IsSemiring R] [AlgebraMap S R] [IsAlgebra S R] : AlgebraMap S (RingQuot r) where
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

instance instIsAlgebra [SemiringOps R] [SemiringOps S] [SMul S R] [IsSemiring R] [AlgebraMap S R] [IsAlgebra S R] : IsAlgebra S (RingQuot r) where
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

def mkRingHom [SemiringOps R] [IsSemiring R] (r: R -> R -> Prop) : R →+* RingQuot r where
  toFun := (⟦·⟧)
  resp_zero := rfl
  resp_one := rfl
  resp_mul := rfl
  resp_add := rfl

def mkRingHom_rel [SemiringOps R] [IsSemiring R] (w: r x y) : mkRingHom r x = mkRingHom r y := Quot.sound (Rel.of w)

def mkRingHom_surj [SemiringOps R] [IsSemiring R] : Function.Surjective (mkRingHom r) := by
  intro x
  cases x with | mk x =>
  exists x

private def preLift [SemiringOps R] [IsSemiring R] [SemiringOps T] [IsSemiring T] {r : R → R → Prop} {f : R →+* T} (h : ∀ ⦃x y⦄, r x y → f x = f y) : RingQuot r →+* T where
  toFun := by
    apply Quot.lift f
    intro _ _ r
    induction r with
    | of r => exact h r
    | add_left _ r' => rw [resp_add, resp_add, r']
    | mul_left _ r' => rw [resp_mul, resp_mul, r']
    | mul_right _ r' => rw [resp_mul, resp_mul, r']
  resp_zero := resp_zero f
  resp_one := resp_one f
  resp_add := by
    rintro ⟨x⟩ ⟨y⟩
    apply resp_add
  resp_mul := by
    rintro ⟨x⟩ ⟨y⟩
    apply resp_mul

def lift [SemiringOps R] [IsSemiring R] [SemiringOps T] [IsSemiring T]: {f: R →+* T // ∀ ⦃x y⦄, r x y → f x = f y } ≃ (RingQuot r →+* T) where
  toFun f := preLift f.property
  invFun f := {
    val := f.comp (mkRingHom r)
    property { x y } eq := by
      show f (mkRingHom _ _) = f (mkRingHom _ _)
      rw [mkRingHom_rel eq]
  }
  leftInv _ := rfl
  rightInv f := by
    dsimp
    apply DFunLike.ext
    rintro ⟨x⟩
    rfl

@[simp]
def lift_mkRingHom_apply [SemiringOps R] [IsSemiring R] [SemiringOps T] [IsSemiring T] (f : R →+* T) {r : R → R → Prop} (w : ∀ ⦃x y⦄, r x y → f x = f y) (x) :
    lift ⟨f, w⟩ (mkRingHom r x) = f x := rfl

def mkAlgHom (S: Type*) [SemiringOps S] [SemiringOps R] [IsSemiring R] [SMul S R] [AlgebraMap S R] [IsAlgebra S R] (r: R -> R -> Prop) : R →ₐ[S] RingQuot r where
  toRingHom := mkRingHom _
  resp_algebraMap _ := rfl

variable (S: Type*) [SemiringOps S] [SemiringOps R] [IsSemiring R] [SMul S R] [AlgebraMap S R] [IsAlgebra S R]
   [SemiringOps A] [IsSemiring A] [AlgebraMap S A] [SMul S A] [IsAlgebra S A]
   [SemiringOps B] [IsSemiring B] [AlgebraMap S B] [SMul S B] [IsAlgebra S B]

def mkAlgHom_surj (r: R -> R -> Prop) : Function.Surjective (mkAlgHom S r) := by
  apply mkRingHom_surj

def preLiftAlgHom {s : A → A → Prop} {f : A →ₐ[S] B }
  (h : ∀ ⦃x y⦄, s x y → f x = f y) : RingQuot s →ₐ[S] B where
  toFun := by
    apply Quot.lift f
    intro a b r
    induction r with
    | of =>
      apply h
      assumption
    | add_left =>
      rw [resp_add, resp_add]
      congr
    | mul_left =>
      rw [resp_mul, resp_mul]
      congr
    | mul_right =>
      rw [resp_mul, resp_mul]
      congr
  resp_zero := resp_zero _
  resp_one := resp_one _
  resp_algebraMap := resp_algebraMap _
  resp_add := by
    intro a b
    cases a, b
    apply resp_add
  resp_mul := by
    intro a b
    cases a, b
    apply resp_mul

def liftAlgHom {s : A → A → Prop} :
  { f : A →ₐ[S] B // ∀ ⦃x y⦄, s x y → f x = f y } ≃ (RingQuot s →ₐ[S] B) where
  toFun f := preLiftAlgHom S f.property
  invFun f := ⟨f.comp (mkAlgHom S s), by
    intro x y r
    show f _ = f _
    congr 1
    apply mkRingHom_rel
    assumption⟩
  leftInv _ := rfl
  rightInv f := by
    apply DFunLike.ext
    rintro ⟨x⟩
    rfl

@[simp]
def liftAlgHom_mkAlgHom_apply (f : A →ₐ[S] B) {s : A → A → Prop}
    (w : ∀ ⦃x y⦄, s x y → f x = f y) (x) : (liftAlgHom S ⟨f, w⟩) ((mkAlgHom S s) x) = f x := rfl

@[ext 1100]
def ringQuot_ext {s : A → A → Prop} (f g : RingQuot s →ₐ[S] B)
    (w : f.comp (mkAlgHom S s) = g.comp (mkAlgHom S s)) : f = g := by
  apply DFunLike.ext
  intro x
  rcases mkAlgHom_surj S s x with ⟨x, rfl⟩
  show (f.comp (mkAlgHom S s)) x = _
  rw [w]; rfl

attribute [irreducible] instZero instOne add mul neg sub npow nsmul zsmul mkRingHom preLift lift preLiftAlgHom liftAlgHom

end RingQuot
