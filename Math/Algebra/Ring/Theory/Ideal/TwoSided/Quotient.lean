import Math.Algebra.Ring.Theory.Ideal.TwoSided.Basic
import Math.Algebra.Ring.Theory.Basic
import Math.Algebra.Ring.Defs
import Math.Algebra.Impls.Unit

namespace Ideal

variable [RingOps R] [IsRing R]

def setoid (i: Ideal R) : Setoid R where
  r a b := a - b ∈ i
  iseqv := {
    refl x := by
      rw [sub_self]
      apply mem_zero
    symm := by
      intro x y h
      rw [←neg_sub]
      apply mem_neg
      assumption
    trans := by
      intro x y z hx hy
      rw [←add_zero (_ - _), ←sub_self y,
        sub_add_assoc, ←add_sub_assoc, add_comm, sub_eq_add_neg, add_assoc (_ + _),
          add_comm _ y, add_comm _ x, ←sub_eq_add_neg, ←sub_eq_add_neg]
      apply mem_add
      assumption
      assumption
  }

def Quot (i: Ideal R) : Type _ := Quotient (setoid i)

@[cases_eliminator]
private def Quot.ind
  {i: Ideal R} {motive: i.Quot -> Prop} : (mk: ∀x: R, motive (Quotient.mk _ x)) -> ∀q, motive q := Quotient.ind

def toRing (i: Ideal R) : Ring i.Quot := by
  apply Ring.ofMinimalAxioms
  case zero => exact Quotient.mk _ 0
  case one => exact Quotient.mk _ 1
  case neg =>
    apply Quotient.lift (fun a => Quotient.mk _ (-a))
    intro a b eq
    apply Quotient.sound
    show _ - _ ∈ i
    rw [neg_sub_neg, ←neg_sub]
    apply mem_neg
    assumption
  case add =>
    apply Quotient.lift₂ (fun a b => Quotient.mk _ (a + b))
    intro a b c d ac bd
    apply Quotient.sound
    show _ - _ ∈ i
    rw [sub_eq_add_neg, neg_add_rev, add_assoc, ←add_assoc b,
      ←sub_eq_add_neg b, add_comm _ (-c), ←add_assoc,
      ←sub_eq_add_neg]
    apply mem_add
    assumption
    assumption
  case mul =>
    apply Quotient.lift₂ (fun a b => Quotient.mk _ (a * b))
    intro a b c d ac bd
    apply Quotient.sound
    show _ - _ ∈ _
    rw [←add_zero (_ - _), ←add_neg_cancel (a * d), sub_add_assoc,
      ←add_assoc (-_), add_comm _ (a * d), add_comm (_ + _),
      ←add_assoc, ←sub_eq_add_neg, ←sub_eq_add_neg,
      ←mul_sub, ←sub_mul]
    apply mem_add
    apply mem_mul_left
    assumption
    apply mem_mul_right
    assumption

  case add_comm =>
    intro a b
    cases a with | mk a =>
    cases b with | mk b =>
    apply Quotient.sound
    rw [add_comm]
  case add_assoc =>
    intro a b c
    cases a with | mk a =>
    cases b with | mk b =>
    cases c with | mk c =>
    apply Quotient.sound
    rw [add_assoc]
  case mul_assoc =>
    intro a b c
    cases a with | mk a =>
    cases b with | mk b =>
    cases c with | mk c =>
    apply Quotient.sound
    rw [mul_assoc]
  case zero_add =>
    intro a
    cases a with | mk a =>
    apply Quotient.sound
    rw [zero_add]
  case neg_add_cancel =>
    intro a
    cases a with | mk a =>
    apply Quotient.sound
    rw [neg_add_cancel]
  case one_mul =>
    intro a
    cases a with | mk a =>
    apply Quotient.sound
    rw [one_mul]
  case mul_one =>
    intro a
    cases a with | mk a =>
    apply Quotient.sound
    rw [mul_one]
  case mul_add =>
    intro a b c
    cases a with | mk a =>
    cases b with | mk b =>
    cases c with | mk c =>
    apply Quotient.sound
    rw [mul_add]
  case add_mul =>
    intro a b c
    cases a with | mk a =>
    cases b with | mk b =>
    cases c with | mk c =>
    apply Quotient.sound
    rw [add_mul]

instance [IsCommMagma R] (i: Ideal R) : IsCommMagma i.toRing where
  mul_comm := by
    intro a b
    induction a using Quot.ind with | mk a =>
    induction b using Quot.ind with | mk b =>
    show Quotient.mk  _ _ =Quotient.mk  _ _
    rw [mul_comm]

-- the canonical projection into the subring generated by the ideal
def mkQuot (i: Ideal R) : R →+* i.toRing where
  toFun := Quotient.mk _
  resp_zero := rfl
  resp_one := rfl
  resp_add := rfl
  resp_mul := rfl

def mkQuot_surj (i: Ideal R) : Function.Surjective i.mkQuot := by
  intro a
  have ⟨x, eq⟩ := Quotient.exists_rep a
  exists x
  rw [←eq]
  rfl

@[simp]
def kernel_mkQuot (i: Ideal R) : Ideal.kernel i.mkQuot = i := by
  ext x
  apply Iff.intro
  intro h
  have : x - 0 ∈ i := Quotient.exact h
  rw [sub_zero] at this
  assumption
  intro h
  apply Quotient.sound
  show _ - _ ∈ i
  rw [sub_zero]; assumption

def eqv_quot_empty : R ≃+* (Ideal.zero R).toRing where
  toFun := mkQuot _
  invFun := by
    apply Quotient.lift (id (α := R))
    intro a b eqv
    apply eq_of_sub_eq_zero
    assumption
  leftInv := by
    intro x
    rfl
  rightInv := by
    intro x
    cases x using Quot.ind
    rfl
  resp_zero := resp_zero _
  resp_one := resp_one _
  resp_add := resp_add _
  resp_mul := resp_mul _

def eqv_quot_univ : Unit ≃+* (Ideal.univ R).toRing :=
  RingEquiv.symm {
    toFun _ := 0
    invFun _ := 0
    leftInv := by
      intro x
      induction x using Quot.ind
      apply Quotient.sound
      trivial
    rightInv _ := rfl
    resp_zero := rfl
    resp_one := rfl
    resp_add := rfl
    resp_mul := rfl
  }

def toRing_eqv_toRing_of_eq {i j: Ideal R} (h: i = j) : i.toRing ≃+* j.toRing where
  toFun := by
    apply Quotient.lift (fun x => mkQuot _ x)
    intro a b eq
    rw [←h]
    apply Quotient.sound
    assumption
  invFun  := by
    apply Quotient.lift (fun x => mkQuot _ x)
    intro a b eq
    rw [h]
    apply Quotient.sound
    assumption
  leftInv := by
    intro a; induction a using Quot.ind
    rfl
  rightInv := by
    intro a; induction a using Quot.ind
    rfl
  resp_zero := rfl
  resp_one := rfl
  resp_add := by
    intro a b
    cases a using Quot.ind
    cases b using Quot.ind
    apply resp_add
  resp_mul := by
    intro a b
    cases a using Quot.ind
    cases b using Quot.ind
    apply resp_mul

end Ideal
