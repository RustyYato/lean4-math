import Math.Algebra.Ring
import Math.Algebra.Hom
import Math.Relation.RelIso

namespace Free.Group

inductive Pre (α: Type u) where
| one
| of  (a: α)
| inv (α: Pre α)
| mul (a b: Pre α)
| pow (a: Pre α) (n: Nat)

scoped instance : One (Pre α) where
  one := .one
scoped instance : Inv (Pre α) where
  inv := .inv
scoped instance : Mul (Pre α) where
  mul := .mul
scoped instance : Pow (Pre α) Nat where
  pow := .pow

inductive Rel : Pre α -> Pre α -> Prop where
| refl (a: Pre α) : Rel a a
| symm : Rel a b -> Rel b a
| trans : Rel a b -> Rel b c -> Rel a c

| one_mul {a: Pre α} : Rel (1 * a) a
| mul_one {a: Pre α} : Rel (a * 1) a
| inv_mul {a: Pre α} : Rel (a⁻¹ * a) 1
| mul_assoc {a b c: Pre α} : Rel (a * b * c) (a * (b * c))

| pow_zero (a: Pre α) : Rel (a ^ 0) 1
| pow_succ (a: Pre α) (n: Nat) : Rel (a ^ (n + 1)) (a ^ n * a)

| inv_congr {a b: Pre α} : Rel a b -> Rel a⁻¹ b⁻¹
| mul_congr {a b c d: Pre α} : Rel a c -> Rel b d -> Rel (a * b) (c * d)

def setoid (α: Type u) : Setoid (Pre α) where
  r := Rel
  iseqv := ⟨.refl, .symm, .trans⟩

def Pre.size : Pre α -> Nat
| 1 | .of _ => 1
| .pow x n => x.size * n + 1
| .mul a b => a.size + b.size
| .inv a => a.size + 1

end Free.Group

def FreeGroup (α: Type u) := Quotient (Free.Group.setoid α)

namespace FreeGroup

open Free.Group

def mk : Pre α -> FreeGroup α := Quotient.mk _

scoped notation "⟦" x "⟧" => FreeGroup.mk x

def ind : {motive: FreeGroup α -> Prop} -> (mk: ∀a, motive ⟦a⟧) -> ∀a, motive a := Quotient.ind
def ind₂ : {motive: FreeGroup α -> FreeGroup α -> Prop} -> (mk: ∀a b, motive ⟦a⟧ ⟦b⟧) -> ∀a b, motive a b := Quotient.ind₂
def ind₃ : {motive: FreeGroup α -> FreeGroup α -> FreeGroup α -> Prop} -> (mk: ∀a b c, motive ⟦a⟧ ⟦b⟧ ⟦c⟧) -> ∀a b c, motive a b c := by
  intro _ h a b c
  induction a, b using ind₂
  induction c using ind
  apply h

instance : One (FreeGroup α) where
  one := ⟦1⟧

instance : Inv (FreeGroup α) where
  inv := by
    apply Quotient.lift (⟦·⁻¹⟧)
    intro a b eq
    apply Quotient.sound
    apply Rel.inv_congr
    assumption

instance : Mul (FreeGroup α) where
  mul := by
    apply Quotient.lift₂ (⟦· * ·⟧)
    intro a b c d ac bd
    apply Quotient.sound
    apply Rel.mul_congr
    assumption
    assumption

instance : Pow (FreeGroup α) Nat where
  pow := flip <| by
    intro n
    apply Quotient.lift (⟦· ^ n⟧)
    intro a b eq
    apply Quotient.sound
    induction n with
    | zero =>
      apply (Rel.pow_zero _).trans
      apply (Rel.pow_zero _).symm
    | succ n ih =>
      apply (Rel.pow_succ _ _).trans
      apply Rel.trans _ (Rel.pow_succ _ _).symm
      apply Rel.mul_congr
      assumption
      assumption

instance : GroupOps (FreeGroup α) where
  zpow := flip zpowRec

instance : IsGroup (FreeGroup α) where
  mul_assoc a b c := by
    induction a, b, c using ind₃
    apply Quotient.sound
    apply Rel.mul_assoc
  one_mul a := by
    induction a using ind
    apply Quotient.sound
    apply Rel.one_mul
  mul_one a := by
    induction a using ind
    apply Quotient.sound
    apply Rel.mul_one
  div_eq_mul_inv _ _ := rfl
  zpow_ofNat _ _ := rfl
  zpow_negSucc _ _ := rfl
  inv_mul_cancel a := by
    induction a using ind
    apply Quotient.sound
    apply Rel.inv_mul
  npow_zero a := by
    induction a using ind
    apply Quotient.sound
    apply Rel.pow_zero
  npow_succ n a := by
    induction a using ind
    apply Quotient.sound
    apply Rel.pow_succ

def Pre.lift [GroupOps G] [IsGroup G] (f: α -> G) : Pre α -> G
| .of x => f x
| .one => 1
| .mul a b => lift f a * lift f b
| .inv a => (lift f a)⁻¹
| .pow a n => lift f a ^ n

def liftAux [GroupOps G] [IsGroup G] (f: α -> G) : FreeGroup α -> G := by
  apply Quotient.lift (Pre.lift f)
  intro a b eq
  induction eq with
  | refl => rfl
  | symm => symm; assumption
  | trans _ _ ih₀ ih₁ => rw [ih₀, ih₁]
  | one_mul => apply one_mul
  | mul_one => apply mul_one
  | inv_mul => apply inv_mul_cancel
  | mul_assoc => apply mul_assoc
  | pow_zero => apply npow_zero
  | pow_succ => apply npow_succ
  | inv_congr =>
    unfold Pre.lift
    congr
  | mul_congr =>
    unfold Pre.lift
    congr

-- lift a function to a group to a group homomorphism from the FreeGroup
def lift [GroupOps G] [IsGroup G] (f: α -> G) : FreeGroup α →* G where
  toFun := liftAux f
  map_one := rfl
  map_mul := by
    intro a b
    induction a, b using ind₂
    rfl

attribute [local instance] Free.Group.setoid

def ι : α ↪ FreeGroup α where
  toFun := mk ∘ .of
  inj' := by
    classical
    intro a b eq
    replace eq := Quotient.exact eq
    generalize ha:Pre.of a = a'
    generalize hb:Pre.of b = b'
    rw [ha, hb] at eq
    induction eq generalizing a b with
    | refl => exact Pre.of.inj (ha.trans hb.symm)
    | symm _ ih =>
      symm
      apply ih
      assumption
      assumption
    | trans _ _ ih₀ ih₁ =>
      subst ha; subst hb
      sorry
    | one_mul
    | mul_one
    | inv_mul
    | mul_assoc
    | pow_zero
    | pow_succ
    | inv_congr
    | mul_congr => contradiction

end FreeGroup
