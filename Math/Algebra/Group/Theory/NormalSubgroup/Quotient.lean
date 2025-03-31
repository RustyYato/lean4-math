import Math.Algebra.Group.Con
import Math.Algebra.Group.Theory.NormalSubgroup.Basic

namespace NormalSubgroup

variable [GroupOps α] [IsGroup α] [GroupOps β] [IsGroup β]

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

protected def Quotient (s: NormalSubgroup α) :=
  IsCon.Quotient s.Con

instance (s: NormalSubgroup α) : GroupOps s.Quotient :=
  inferInstanceAs (GroupOps (IsCon.Quotient s.Con))
instance (s: NormalSubgroup α) : IsGroup s.Quotient :=
  inferInstanceAs (IsGroup (IsCon.Quotient s.Con))

def mkQuot (s: NormalSubgroup α) : α →* s.Quotient :=
  IsMulCon.mkQuot _

def mkQuot_kernel (s: NormalSubgroup α) : s = kernel s.mkQuot := by
  ext x
  apply Iff.intro
  intro h
  apply Quotient.sound
  show x / 1 ∈ s
  rwa [div_one]
  intro h
  replace h := Quotient.exact h
  rwa [←div_one x]

noncomputable def image_equiv (f: α →* β) : (kernel f).Quotient ≃* Subgroup.range f where
  toFun := by
    refine Quotient.lift ?_ ?_
    intro a
    exact ⟨f a, Set.mem_range'⟩
    intro a b h
    congr 1
    apply eq_of_div_eq_one
    rwa [←map_div]
  invFun f := mkQuot _ (Classical.choose f.property)
  leftInv := by
    intro x
    induction x using IsCon.Quotient.ind with | mk x =>
    simp
    apply Quotient.sound
    show f (_ / x) = 1
    have : f x ∈ (Subgroup.range f) := Set.mem_range'
    rw [map_div, (Classical.choose_spec this), div_self]
  rightInv := by
    intro x
    simp
    apply Subtype.val_inj
    show f (Classical.choose _) = x.val
    symm; exact Classical.choose_spec x.property
  map_one := by
    simp
    apply Subtype.val_inj
    apply map_one f
  map_mul := by
    intro x y
    induction x using IsCon.Quotient.ind with | mk x =>
    induction y using IsCon.Quotient.ind with | mk y =>
    apply Subtype.val_inj
    apply map_mul f

end NormalSubgroup
