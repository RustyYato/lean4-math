import Math.Algebra.Ring.Theory.Ideal.TwoSided.Basic
import Math.Algebra.Ring.Theory.Basic
import Math.Algebra.Ring.Theory.Subring
import Math.Algebra.Ring.Defs
import Math.Algebra.Impls.Unit
import Math.Algebra.Ring.Con

namespace Ideal

variable [RingOps R] [IsRing R] [RingOps S] [IsRing S]

protected def Con (i: Ideal R) : RingCon R where
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
  resp_add := by
    intro a b c d ac bd
    show (a + b) - (c + d) ∈ i
    rw [sub_add, add_sub_assoc, add_comm, add_sub_assoc]
    apply mem_add
    assumption
    assumption
  resp_mul := by
    intro a b c d ac bd
    show a * b - c * d ∈ i
    rw [←add_zero (a * b), ←neg_add_cancel (a * d), ←add_assoc,
      ←sub_eq_add_neg, add_sub_assoc, ←mul_sub, ←sub_mul]
    apply mem_add
    apply mem_mul_left
    assumption
    apply mem_mul_right
    assumption

protected def toRing (i: Ideal R) := IsCon.Quotient i.Con

instance (i: Ideal R) : RingOps i.toRing := inferInstanceAs (RingOps (IsCon.Quotient i.Con))
instance (i: Ideal R) : IsRing i.toRing := inferInstanceAs (IsRing (IsCon.Quotient i.Con))
instance [IsCommMagma R] (i: Ideal R) : IsCommMagma i.toRing := inferInstanceAs (IsCommMagma (IsCon.Quotient i.Con))

-- the canonical projection into the subring generated by the ideal
def mkQuot (i: Ideal R) : R →+* i.toRing where
  toFun := Quotient.mk _
  map_zero := rfl
  map_one := rfl
  map_add := rfl
  map_mul := rfl

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
  map_zero := map_zero _
  map_one := map_one _
  map_add := map_add _
  map_mul := map_mul _

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
    map_zero := rfl
    map_one := rfl
    map_add := rfl
    map_mul := rfl
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
  map_zero := rfl
  map_one := rfl
  map_add := by
    intro a b
    cases a using Quot.ind
    cases b using Quot.ind
    simp
    apply map_add (mkQuot j)
  map_mul := by
    intro a b
    cases a using Quot.ind
    cases b using Quot.ind
    apply map_mul

def image_embed (f: R →+* S) : (kernel f).toRing ↪+* Subring.range f where
  toFun := by
    refine Quotient.lift ?_ ?_
    intro a
    exact ⟨f a, Set.mem_range'⟩
    intro a b h
    congr 1
    apply eq_of_sub_eq_zero
    rw [←map_sub, h]
  inj' := by
    intro x y h
    induction x; induction y
    have := Subtype.mk.inj h
    apply Quotient.sound
    show f (_ - _) = 0
    rw [map_sub, this, sub_self]
  map_zero := by
    apply Subtype.val_inj
    apply map_zero f
  map_one := by
    apply Subtype.val_inj
    apply map_one f
  map_add := by
    intro x y
    induction x using IsCon.Quotient.ind with | mk x =>
    induction y using IsCon.Quotient.ind with | mk y =>
    apply Subtype.val_inj
    apply map_add f
  map_mul := by
    intro x y
    induction x using IsCon.Quotient.ind with | mk x =>
    induction y using IsCon.Quotient.ind with | mk y =>
    apply Subtype.val_inj
    apply map_mul f

noncomputable def image_equiv (f: R →+* S) : (kernel f).toRing ≃+* Subring.range f := {
  image_embed f with
  invFun f := mkQuot _ (Classical.choose f.property)
  leftInv := by
    intro x
    induction x using IsCon.Quotient.ind with | mk x =>
    simp
    apply Quotient.sound
    show f (_ - x) = 0
    have : f x ∈ (Subring.range f) := Set.mem_range'
    rw [map_sub, (Classical.choose_spec this), sub_self]
  rightInv := by
    intro x
    simp
    apply Subtype.val_inj
    show f (Classical.choose _) = x.val
    symm; exact Classical.choose_spec x.property
}

end Ideal
