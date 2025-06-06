import Math.Algebra.GradedMonoid.Defs
import Math.Algebra.DirectSum.Defs

class IsGNonUnitalNonAssocSemiring (A: γ -> Type*) [Add γ]
  [∀i: γ, AddMonoidOps (A i)]
  [GMul A]: Prop where
  [toAddMonoid (i: γ) : IsAddMonoid (A i)]
  [toAddCommMagma: ∀i: γ, IsAddCommMagma (A i)]
  mul_zero : ∀{i j} (a: A i), GMul.gMul a (0: A j) = 0
  zero_mul : ∀{i j} (a: A j), GMul.gMul (0: A i) a = 0
  mul_add : ∀{i j} (k: A i) (a b: A j), GMul.gMul k (a + b) = GMul.gMul k a + GMul.gMul k b
  add_mul : ∀{i j} (a b: A i) (k: A j), GMul.gMul (a + b) k = GMul.gMul a k + GMul.gMul b k

class GSemiringOps (A: γ -> Type*) [AddMonoidOps γ] extends GMonoidOps A where
  natCast : ℕ -> A 0

class IsGSemiring (A: γ -> Type*) [AddMonoidOps γ] [IsAddMonoid γ]
  [∀i: γ, AddMonoidOps (A i)]
  [GSemiringOps A]: Prop extends IsGNonUnitalNonAssocSemiring A, IsGMonoid A where
  natCast_zero : GSemiringOps.natCast 0 = (0: A 0)
  natCast_succ (n: ℕ) : GSemiringOps.natCast (n + 1) = (GSemiringOps.natCast n: A 0) + GOne.gOne

class GRingOps (A: γ -> Type*) [AddMonoidOps γ] extends GSemiringOps A where
  intCast : ℤ -> A 0

class IsGRing (A: γ -> Type*) [AddMonoidOps γ] [IsAddMonoid γ]
  [∀i: γ, AddGroupOps (A i)]
  [GRingOps A]: Prop extends IsGSemiring A, IsGMonoid A where
  [toAddGroup (i: γ) : IsAddGroup (A i)]
  intCast_ofNat (n: ℕ) : GRingOps.intCast n = (GSemiringOps.natCast n: A 0)
  intCast_negSucc (n: ℕ) : GRingOps.intCast (Int.negSucc n) = -(GSemiringOps.natCast (n + 1): A 0)

namespace DirectSum

variable {A : γ -> Type*} [DecidableEq γ]

section

variable [Add γ] [∀i, AddMonoidOps (A i)] [GMul A] [instRing: IsGNonUnitalNonAssocSemiring A]

private instance : ∀i, IsAddMonoid (A i) := instRing.toAddMonoid
private instance : ∀i, IsAddCommMagma (A i) := instRing.toAddCommMagma

private def preMul (a: A i) (j: γ) : A j →+ (⊕i, A i) where
  toFun b := ι _ (GMul.gMul a b)
  map_zero := by rw [instRing.mul_zero, map_zero]
  map_add {x y} := by rw [instRing.mul_add, map_add]

def mulHom : (⊕i, A i) →+ (⊕i, A i) →+ (⊕i, A i) :=
  lift fun i => {
    toFun a := lift (preMul a)
    map_zero := by
      unfold preMul
      conv => {
        lhs; rhs; intro j; lhs; lhs; intro b
        rw [instRing.zero_mul, map_zero]
      }
      apply lift.map_zero
    map_add {x y} := by
      conv => {
        lhs
        unfold preMul
        rhs; intro j; lhs; lhs; intro b
        rw [instRing.add_mul, map_add]
      }
      show lift (preMul x + preMul y) = _
      apply lift.map_add
  }

def mulHom_ι (a: A i) (b: A j) : mulHom (ι i a) (ι j b) = ι (i + j) (GMul.gMul a b) := by
  unfold mulHom
  erw [lift_ι, lift_ι]
  rfl

instance : Mul (⊕i, A i) where
  mul a b := mulHom a b

def mul_ι (a: A i) (b: A j) : (ι i a) * (ι j b) = ι (i + j) (GMul.gMul a b) := by
  apply mulHom_ι

attribute [irreducible] mulHom

def mul_eq_mulHom (a b: ⊕i, A i) : a * b = mulHom a b := rfl

instance : IsNonUnitalNonAssocSemiring (⊕i, A i) where
  zero_mul a := by
    rw [mul_eq_mulHom, map_zero]; rfl
  mul_zero a := by
    rw [mul_eq_mulHom, map_zero]
  mul_add k a b := by
    rw [mul_eq_mulHom, mul_eq_mulHom, mul_eq_mulHom, map_add]
  add_mul a b k := by
    rw [mul_eq_mulHom, mul_eq_mulHom, mul_eq_mulHom, map_add]
    rfl

private def add_congr [Add α] (a b c d: α) : a = c -> b = d -> a + b = c + d := by
  rintro rfl rfl ; rfl

instance [IsAddCommMagma γ] [IsGCommMagma A] : IsCommMagma (⊕i, A i) where
  mul_comm a b := by
    simp [mul_eq_mulHom]
    induction a with
    | zero =>
      erw [map_zero, map_zero]
      rfl
    | ι i a =>
      induction b with
      | zero =>
        erw [map_zero, map_zero]
        rfl
      | ι j b =>
        repeat rw [mulHom_ι]
        let a' : GradedMonoid A := GradedMonoid.mk a
        let b' : GradedMonoid A := GradedMonoid.mk b
        let x := a' * b'
        let y := b' * a'
        show ι x.fst x.snd = ι y.fst y.snd
        suffices x = y by rw [this]
        apply mul_comm
      | add =>
        repeat erw [map_add]
        apply add_congr
        assumption
        assumption
    | add =>
      repeat erw [map_add]
      apply add_congr
      assumption
      assumption

end

section

variable [AddMonoidOps γ] [IsAddMonoid γ] [∀i, AddMonoidOps (A i)] [GSemiringOps A] [IsGSemiring A]

instance : NatCast (⊕i, A i) where
  natCast n := ι 0 (GSemiringOps.natCast n)

instance : One (⊕i, A i) where
  one := ι 0 GOne.gOne

instance : Pow (⊕i, A i) ℕ := instNPowrec

def natCast_eq (n: ℕ) : n = ι 0 (GSemiringOps.natCast n: A 0) := rfl
def one_eq : 1 = ι 0 (GOne.gOne: A 0) := rfl

instance : IsSemigroup (⊕i, A i) where
  mul_assoc a b c := by
    simp [mul_eq_mulHom]
    induction a with
    | zero =>
      erw [map_zero, map_zero]
      rfl
    | ι i a =>
      induction b with
      | zero =>
        erw [map_zero, map_zero, map_zero]
        rfl
      | ι j b =>
        rw [mulHom_ι]
        induction c with
        | zero =>
          erw [map_zero, map_zero, map_zero]
        | ι k c =>
          repeat rw [mulHom_ι]
          let a' : GradedMonoid A := GradedMonoid.mk a
          let b' : GradedMonoid A := GradedMonoid.mk b
          let c' : GradedMonoid A := GradedMonoid.mk c
          let x := a' * b' * c'
          let y := a' * (b' * c')
          show ι x.fst x.snd = ι y.fst y.snd
          suffices x = y by rw [this]
          apply mul_assoc
        | add =>
          repeat erw [map_add]
          apply add_congr
          assumption
          assumption
      | add =>
        repeat erw [map_add]
        apply add_congr
        assumption
        assumption
    | add =>
      repeat erw [map_add]
      apply add_congr
      assumption
      assumption

instance : IsSemiring (⊕i, A i) where
  natCast_zero := by
    ext i
    show ι 0 (GSemiringOps.natCast 0) i = _
    rw [IsGSemiring.natCast_zero, apply_ι]
    split; subst i; rfl; rfl
  natCast_succ n := by
    ext i
    rw [natCast_eq, natCast_eq, one_eq]
    simp; rw [apply_ι, apply_ι, apply_ι]
    split; subst i
    apply IsGSemiring.natCast_succ
    rw [add_zero]
  mul_one a := by
    induction a with
    | zero => rw [mul_eq_mulHom, map_zero]; rfl
    | add => rw [mul_eq_mulHom, map_add]; apply add_congr <;> assumption
    | ι i a =>
      rw [one_eq, mul_eq_mulHom, mulHom_ι]
      let a' := GradedMonoid.mk a
      let b' : GradedMonoid A := 1
      let x := a' * b'
      show ι x.fst x.snd = ι a'.fst a'.snd
      suffices x = a' by rw [this]
      apply mul_one
  one_mul a := by
    induction a with
    | zero => rw [mul_eq_mulHom, map_zero]
    | add => rw [mul_eq_mulHom, map_add]; apply add_congr <;> assumption
    | ι i a =>
      rw [one_eq, mul_eq_mulHom, mulHom_ι]
      let a' := GradedMonoid.mk a
      let b' : GradedMonoid A := 1
      let x := b' * a'
      show ι x.fst x.snd = ι a'.fst a'.snd
      suffices x = a' by rw [this]
      apply one_mul

end

section

variable [AddMonoidOps γ] [IsAddMonoid γ] [∀i, AddGroupOps (A i)] [GRingOps A] [instRing: IsGRing A]

private instance : ∀i, IsAddGroup (A i) := instRing.toAddGroup

instance : IntCast (⊕i, A i) where
  intCast n := ι 0 (GRingOps.intCast n)

def intCast_eq (n: ℤ) : n = ι 0 (GRingOps.intCast n: A 0) := rfl

instance : IsRing (⊕i, A i) where
  intCast_ofNat n := by rw [intCast_eq, natCast_eq, IsGRing.intCast_ofNat]
  intCast_negSucc n := by rw [intCast_eq, natCast_eq, IsGRing.intCast_negSucc, map_neg]

end

section

variable [AddMonoidOps γ] [IsAddMonoid γ] [∀i, AddMonoidOps (A i)] [GSemiringOps A] [IsGSemiring A]
  [SemiringOps R] [IsSemiring R]

def evalRing (f: ∀i, A i →+ R) (hone: f 0 GOne.gOne = 1) (hmul: ∀{i j} (a b), f _ (GMul.gMul a b) = f i a * f j b) : (⊕i, A i) →+* R := {
    eval f with
    map_one := by
      simp [one_eq]
      rw [eval_ι]
      apply hone
    map_mul {a b} := by
      simp
      induction a with
      | zero => simp [map_zero]
      | add =>
          rw [add_mul, map_add, map_add, add_mul]
          congr
      | ι i a =>
        induction b with
        | zero => simp [map_zero]
        | add =>
          rw [mul_add, map_add, map_add, mul_add]
          congr
        | ι j b => rw [mul_ι, eval_ι, eval_ι, eval_ι, hmul]
  }

def evalRing_ι (f: ∀i, A i →+ R) (hone hmul) : evalRing f hone hmul (ι i a) = f i a := eval_ι _ _

def liftRing : { f: ∀i, A i →+ R // f 0 GOne.gOne = 1 ∧ ∀{i j} (a b), f _ (GMul.gMul a b) = f i a * f j b } ≃ ((⊕i, A i) →+* R):= {
  toFun f := evalRing f.1 f.property.1 f.property.2
  invFun f := ⟨fun i => f.toAddGroupHom.comp (ι i), by
    apply map_one f, by
    intro i j a b
    simp; rw [←mul_ι, map_mul f]⟩
  leftInv f := by
    simp; congr; ext i a
    simp
    rw [evalRing_ι]
  rightInv f := by
    ext a
    show lift (lift.symm f.toAddGroupHom) _ = f a
    simp
}

def liftRing_ι (f) : liftRing (A := A) (R := R) f (ι i a) = f.val i a := evalRing_ι _ f.property.1 f.property.2

def apply_lift_eq_apply_liftRing (f: ∀i, A i →+ R) (hone hmul) : lift f a = liftRing ⟨f, hone, hmul⟩ a := rfl

instance : One (A 0) := ⟨GOne.gOne⟩
instance : Mul (A 0) where
  mul a b := cast (by rw [add_zero]) (GMul.gMul a b)

def ιHom : A 0 →+* ⊕i, A i := {
  ι 0 with
  map_one := rfl
  map_mul {a b } := by
    simp; rw [mul_ι]
    let a' := GradedMonoid.mk a
    let b' := GradedMonoid.mk b
    let x := a' * b'
    let y := GradedMonoid.mk (a * b)
    show ι y.fst y.snd = ι x.fst x.snd
    suffices x = y by rw [this]
    ext; apply add_zero
    symm; apply cast_heq
}

end

end DirectSum
