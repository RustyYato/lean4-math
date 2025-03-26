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

@[cases_eliminator]
private def Quot.ind₂
  {i: Ideal R} {motive: i.Quot -> i.Quot -> Prop} : (mk: ∀a b: R, motive (Quotient.mk _ a) (Quotient.mk _ b)) -> ∀a b, motive a b := Quotient.ind₂

@[cases_eliminator]
private def Quot.ind₃
  {i: Ideal R} {motive: i.Quot -> i.Quot -> i.Quot -> Prop} : (mk: ∀a b c: R, motive (Quotient.mk _ a) (Quotient.mk _ b) (Quotient.mk _ c)) -> ∀a b c, motive a b c := by
  intro h a b c
  cases a, b
  cases c
  apply h

section

variable {i: Ideal R}

instance : Zero i.Quot where
  zero :=  Quotient.mk _ 0
instance : One i.Quot where
  one :=  Quotient.mk _ 1
instance : OfNat i.Quot (n + 2) where
  ofNat := Quotient.mk _ (OfNat.ofNat (n + 2))
instance : NatCast i.Quot where
  natCast n := Quotient.mk _ n
instance : IntCast i.Quot where
  intCast n := Quotient.mk _ n

private def resp_add' (a b c d: R) (ac: a - c ∈ i) (bd: b - d ∈ i) : (a + b) - (c + d) ∈ i := by
  rw [sub_eq_add_neg, neg_add_rev, add_assoc, ←add_assoc b,
    ←sub_eq_add_neg b, add_comm _ (-c), ←add_assoc,
    ←sub_eq_add_neg]
  apply mem_add
  assumption
  assumption

private def resp_mul' (a b c d) (ac: a - c ∈ i) (bd: b - d ∈ i) : (a * b) - (c * d) ∈ i := by
  rw [←add_zero (_ - _), ←add_neg_cancel (a * d), sub_add_assoc,
    ←add_assoc (-_), add_comm _ (a * d), add_comm (_ + _),
    ←add_assoc, ←sub_eq_add_neg, ←sub_eq_add_neg,
    ←mul_sub, ←sub_mul]
  apply mem_add
  apply mem_mul_left
  assumption
  apply mem_mul_right
  assumption

private def resp_neg' (a b) (ac: a - b ∈ i) : (-a) - (-b) ∈ i := by
  rw [neg_sub_neg, ←neg_sub]
  apply mem_neg
  assumption

private def resp_nsmul' (n: ℕ) (a b: R) (ab: a - b ∈ i) : (n • a) - (n • b) ∈ i := by
  induction n with
  | zero => simp; apply mem_zero
  | succ n ih =>
    rw [succ_nsmul, succ_nsmul]
    apply resp_add' <;> assumption

instance : Add i.Quot where
  add := by
    apply Quotient.lift₂ (fun a b => Quotient.mk _ (a + b))
    intro a b c d ac bd
    apply Quotient.sound
    apply resp_add' <;> assumption

instance : Mul i.Quot where
  mul := by
    apply Quotient.lift₂ (fun a b => Quotient.mk _ (a * b))
    intro a b c d ac bd
    apply Quotient.sound
    apply resp_mul' <;> assumption

instance : Neg i.Quot where
  neg := by
    apply Quotient.lift (fun a => Quotient.mk _ (-a))
    intro a b eq
    apply Quotient.sound
    show _ - _ ∈ i
    rw [neg_sub_neg, ←neg_sub]
    apply mem_neg
    assumption

instance : Sub i.Quot where
  sub := by
    apply Quotient.lift₂ (fun a b => Quotient.mk _ (a - b))
    intro a b c d ac bd
    apply Quotient.sound
    rw [sub_eq_add_neg, sub_eq_add_neg]
    apply resp_add'
    assumption
    apply resp_neg'
    assumption

instance : SMul ℕ i.Quot where
  smul n := by
    apply Quotient.lift (fun a => Quotient.mk _ (n • a))
    intro a b eq
    apply Quotient.sound
    apply resp_nsmul'
    assumption

instance : SMul ℤ i.Quot where
  smul n := by
    apply Quotient.lift (fun a => Quotient.mk _ (n • a))
    intro a b eq
    apply Quotient.sound
    cases n
    rw [zsmul_ofNat, zsmul_ofNat]
    apply resp_nsmul'
    assumption
    rw [zsmul_negSucc, zsmul_negSucc]
    apply resp_neg'
    apply resp_nsmul'
    assumption

instance : Pow i.Quot ℕ where
  pow := flip <| by
    intro n
    apply Quotient.lift (fun a => Quotient.mk _ (a ^ n))
    intro a b eq
    apply Quotient.sound
    induction n with
    | zero => rw [npow_zero, npow_zero]
    | succ n ih =>
      rw [npow_succ, npow_succ, ]
      apply resp_mul' <;> assumption

instance : IsRing i.Quot where
  add_comm a b := by
    cases a, b
    apply Quotient.sound
    rw [add_comm]
  add_assoc a b c := by
    cases a, b, c
    apply Quotient.sound
    rw [add_assoc]
  zero_add a := by
    cases a
    apply Quotient.sound
    rw [zero_add]
  add_zero a := by
    cases a
    apply Quotient.sound
    rw [add_zero]
  natCast_zero := by
    apply Quotient.sound
    rw [natCast_zero]
  natCast_succ n := by
    apply Quotient.sound
    rw [natCast_succ]
  ofNat_eq_natCast n := by
    apply Quotient.sound
    rw [ofNat_eq_natCast]
  mul_assoc a b c := by
    cases a, b, c
    apply Quotient.sound
    rw [mul_assoc]
  zero_mul a := by
    cases a
    apply Quotient.sound
    rw [zero_mul]
  mul_zero a := by
    cases a
    apply Quotient.sound
    rw [mul_zero]
  one_mul a := by
    cases a
    apply Quotient.sound
    rw [one_mul]
  mul_one a := by
    cases a
    apply Quotient.sound
    rw [mul_one]
  left_distrib a b c := by
    cases a, b, c
    apply Quotient.sound
    rw [mul_add]
  right_distrib a b c := by
    cases a, b, c
    apply Quotient.sound
    rw [add_mul]
  sub_eq_add_neg a b := by
    cases a, b
    apply Quotient.sound
    rw [sub_eq_add_neg]
  zsmul_ofNat n a := by
    cases a
    apply Quotient.sound
    rw [zsmul_ofNat]
  zsmul_negSucc n a := by
    cases a
    apply Quotient.sound
    rw [zsmul_negSucc]
  neg_add_cancel a := by
    cases a
    apply Quotient.sound
    rw [neg_add_cancel]
  intCast_ofNat n := by
    apply Quotient.sound
    rw [intCast_ofNat]
  intCast_negSucc n := by
    apply Quotient.sound
    rw [intCast_negSucc]
  zero_nsmul a := by
    cases a
    apply Quotient.sound
    rw [zero_nsmul]
  succ_nsmul n a := by
    cases a
    apply Quotient.sound
    rw [succ_nsmul]
  npow_zero a := by
    cases a
    apply Quotient.sound
    rw [npow_zero]
  npow_succ n a := by
    cases a
    apply Quotient.sound
    rw [npow_succ]

def toRing (i: Ideal R) : Ring i.Quot where

instance [IsCommMagma R] (i: Ideal R) : IsCommMagma i.toRing where
  mul_comm := by
    intro a b
    induction a using Quot.ind with | mk a =>
    induction b using Quot.ind with | mk b =>
    show Quotient.mk  _ _ =Quotient.mk  _ _
    rw [mul_comm]

end

-- the canonical projection into the subring generated by the ideal
def mkQuot (i: Ideal R) : R →+* i.toRing where
  toFun := Quotient.mk _
  resp_zero' := rfl
  resp_one' := rfl
  resp_add' := rfl
  resp_mul' := rfl

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

def mkQuot_eq_zero_iff (i: Ideal R) (a: R) : i.mkQuot a = 0 ↔ a ∈ i := by
  apply Iff.intro
  intro h
  rw [←sub_zero a]
  exact Quotient.exact h
  intro h
  rw [←sub_zero a] at h
  apply Quotient.sound
  assumption

@[induction_eliminator]
def toRing_induction {i: Ideal R} {motive: i.toRing -> Prop} : (mk: ∀a, motive (i.mkQuot a)) -> ∀q, motive q := by
  intro h q
  obtain ⟨a, rfl⟩ := i.mkQuot_surj q
  apply h

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
  resp_zero' := resp_zero _
  resp_one' := resp_one _
  resp_add' := resp_add _
  resp_mul' := resp_mul _

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
    resp_zero' := rfl
    resp_one' := rfl
    resp_add' := rfl
    resp_mul' := rfl
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
  resp_zero' := rfl
  resp_one' := rfl
  resp_add' := by
    intro a b
    cases a using Quot.ind
    cases b using Quot.ind
    apply resp_add
  resp_mul' := by
    intro a b
    cases a using Quot.ind
    cases b using Quot.ind
    apply resp_mul

end Ideal
