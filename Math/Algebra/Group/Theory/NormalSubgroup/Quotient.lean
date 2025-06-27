import Math.Algebra.Group.Con
import Math.Algebra.Group.Theory.NormalSubgroup.Basic

namespace NormalSubgroup

variable [GroupOps α] [IsGroup α] [GroupOps β] [IsGroup β]

protected def ofCon (c: MulCon α) : NormalSubgroup α where
  carrier := Set.mk (c 1 ·)
  mem_one := c.refl _
  mem_mul := by
    intro a b ha hb
    show c 1 (a * b)
    rw [←mul_one 1]
    apply resp_mul
    assumption
    assumption
  mem_inv := by
    intro a ha
    show c 1 (a⁻¹)
    rw [←inv_one]
    apply resp_inv
    assumption
  mem_conj := by
    intro x a ha
    simp
    rw [←map_one (Group.conj x)]
    rw [Group.apply_conj, Group.apply_conj]
    apply resp_mul
    apply resp_mul
    rfl; assumption; rfl

protected def Con (s: NormalSubgroup α) : MulCon α where
  r a b := a / b ∈ s
  iseqv := {
    refl x := by
      rw [div_self]
      apply mem_one
    symm {x y} h := by
      rw [div_eq_mul_inv, ←inv_inv (y * x⁻¹), inv_mul_rev,
        inv_inv, ←div_eq_mul_inv]
      apply mem_inv
      assumption
    trans {a b c} h g := by
      rw [←mul_one a, ←inv_mul_cancel b, ←mul_assoc, div_eq_mul_inv, mul_assoc,
        ←div_eq_mul_inv, ←div_eq_mul_inv]
      apply mem_mul
      assumption
      assumption
  }
  resp_mul := by
    intro a b c d h g
    show (a * b) / (c * d) ∈ s
    rw [div_eq_mul_inv, inv_mul_rev, ←mul_assoc, mul_assoc a,
      ←div_eq_mul_inv b d, ←mul_one a, ←inv_mul_cancel c, ←mul_assoc,
      ←div_eq_mul_inv a, mul_assoc (a / c), mul_assoc (a / c)]
    apply mem_mul
    assumption
    rw (occs := [1]) [←inv_inv c]
    apply mem_conj
    assumption

def equivCon : NormalSubgroup α ≃ MulCon α where
  toFun := NormalSubgroup.Con
  invFun := NormalSubgroup.ofCon
  leftInv s := by
    ext x
    apply Iff.trans (Relation.symm_iff (r := s.Con))
    show x / 1 ∈ s ↔ x ∈ s
    rw [div_one]
  rightInv c := by
    apply le_antisymm
    intro a b
    show c 1 (a / b) -> _
    intro h
    have := resp_mul c (z := b) h (by rfl)
    rw [one_mul, div_mul_cancel] at this
    apply Relation.symm
    assumption
    intro a b h
    have := resp_mul c (z := a⁻¹) h (by rfl)
    rw [mul_inv_cancel, ←div_eq_mul_inv] at this
    have := resp_inv _ this
    rwa [inv_one, inv_div] at this

protected def Quotient (s: NormalSubgroup α) :=
  AlgQuotient s.Con

instance (s: NormalSubgroup α) : GroupOps s.Quotient :=
  inferInstanceAs (GroupOps (AlgQuotient s.Con))
instance (s: NormalSubgroup α) : IsGroup s.Quotient :=
  inferInstanceAs (IsGroup (AlgQuotient s.Con))
instance [IsCommMagma α] (s: NormalSubgroup α) : IsCommMagma s.Quotient :=
  inferInstanceAs (IsCommMagma (AlgQuotient s.Con))

def mkQuot (s: NormalSubgroup α) : α ↠* s.Quotient :=
  MulCon.mkQuot _

@[induction_eliminator]
def ind {s: NormalSubgroup α} {motive: s.Quotient -> Prop} (mk: ∀a, motive (s.mkQuot a)) : ∀q, motive q := AlgQuotient.ind mk

def mkQuot_kernel (s: NormalSubgroup α) : s = kernel s.mkQuot.toGroupHom := by
  ext x
  apply Iff.intro
  intro h
  apply Quotient.sound
  show x / 1 ∈ s
  rwa [div_one]
  intro h
  replace h := Quotient.exact h
  rwa [←div_one x]

def kernel_bij_range (f: α →* β) : (kernel f).Quotient ⇔* Subgroup.range f where
  toFun := by
    refine Quotient.lift ?_ ?_
    intro a
    exact ⟨f a, Set.mem_range'⟩
    intro a b h
    congr 1
    apply eq_of_div_eq_one
    rwa [←map_div]
  map_one := by
    apply Subtype.val_inj
    apply map_one f
  map_mul {a b} := by
    induction a; induction b
    apply Subtype.val_inj
    apply map_mul f
  inj' := by
    intro a b h
    induction a; induction b
    replace h := Subtype.mk.inj h
    apply Quotient.sound
    show f _ = _
    rw [map_div, h, div_self]
  surj' := by
    intro ⟨_, a, rfl⟩
    exact ⟨(kernel f).mkQuot a, rfl⟩

noncomputable def kernel_equiv_range (f: α →* β) : (kernel f).Quotient ≃* Subgroup.range f := {
  Bijection.toEquiv (kernel_bij_range f).toBijection, kernel_bij_range f with
}

end NormalSubgroup
