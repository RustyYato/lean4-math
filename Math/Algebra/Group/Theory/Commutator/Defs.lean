import Math.Algebra.GroupQuot.Defs

-- every product is related to the product with it's arguments swapped
inductive Commutator.Rel (α: Type*) [Mul α] : α -> α -> Prop where
| intro (a b) : Rel α (a * b) (b * a)

def Commutator (M: Type*) [MonoidOps M] [IsMonoid M] :=
  GroupQuot (Commutator.Rel M)

namespace Commutator

instance (M: Type*) [MonoidOps M] [IsMonoid M] : MonoidOps (Commutator M) := GroupQuot.instMonoidOps
instance (M: Type*) [MonoidOps M] [IsMonoid M] : IsMonoid (Commutator M) := GroupQuot.instIsMonoid

instance (G: Type*) [GroupOps G] [IsGroup G] : MonoidOps (Commutator G) := GroupQuot.instMonoidOps
instance (G: Type*) [GroupOps G] [IsGroup G] : IsMonoid (Commutator G) := GroupQuot.instIsMonoid

variable [MonoidOps M] [IsMonoid M] [MonoidOps G] [IsMonoid G]

def mk : M →* Commutator M := GroupQuot.mk _

@[induction_eliminator]
def ind {motive: Commutator M -> Prop} : (mk: ∀m, motive (mk m)) -> ∀x, motive x := GroupQuot.ind

instance (M: Type*) [MonoidOps M] [IsMonoid M] : IsCommMagma (Commutator M) where
  mul_comm := by
    intro a b
    induction a with | mk a =>
    induction b with | mk b =>
    rw [←map_mul, ←map_mul]
    apply GroupQuot.mk_rel
    apply Commutator.Rel.intro

def lift : { f: M →* G // ∀a b: M, f (a * b) = f (b * a) } ≃ (Commutator M →* G) :=
  Equiv.symm <| Equiv.trans GroupQuot.lift.symm <| Equiv.congrSubtype .rfl <| by
    intro f
    apply Iff.intro
    intro h x y
    apply h
    apply Rel.intro
    intro h x y r
    cases r
    apply h

def liftComm [IsCommMagma G] : (M →* G) ≃ (Commutator M →* G) :=
  Equiv.symm <| Equiv.trans lift.symm <| {
    toFun f := f.val
    invFun f := {
      val := f
      property := by
        intro a b
        rw [map_mul, map_mul, mul_comm]
    }
    leftInv f := rfl
    rightInv f := rfl
  }

def lift_mk (f: { f: M →* G // ∀a b: M, f (a * b) = f (b * a) }) (x: M) : lift f (mk x) = f.val x :=
  GroupQuot.lift_mk_apply _ _ _

def lift_comp_mk (f: { f: M →* G // ∀a b: M, f (a * b) = f (b * a) }) : (lift f).comp mk = f.val :=
  GroupHom.ext _ _ (lift_mk _)

def symm_lift_mk (f: Commutator M →* G) (x: M) : (lift.symm f).val x = f (mk x) :=
  GroupQuot.symm_lift_mk_apply _ _

def liftComm_mk [IsCommMagma G] (f: M →* G) (x: M) : liftComm f (mk x) = f x :=
  GroupQuot.lift_mk_apply _ _ _

def liftComm_comp_mk [IsCommMagma G] (f: M →* G) : (liftComm f).comp mk = f :=
  GroupHom.ext _ _ (lift_mk _)

def symm_liftComm_mk [IsCommMagma G] (f: Commutator M →* G) (x: M) : liftComm.symm f x = f (mk x) :=
  GroupQuot.symm_lift_mk_apply _ _

def equivComm [IsCommMagma M] : M ≃ Commutator M where
  toFun := liftComm.symm (.id _)
  invFun := liftComm (.id _)
  leftInv x := by simp [symm_liftComm_mk, liftComm_mk]
  rightInv x := by
    induction x with
    | mk x =>
    simp [symm_liftComm_mk, liftComm_mk]

end Commutator
