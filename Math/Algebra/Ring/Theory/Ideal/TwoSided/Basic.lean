import Math.Algebra.Ring.Theory.Ideal.Defs
import Math.Algebra.Hom.Defs
import Math.Algebra.Group.Hom
import Math.Algebra.Monoid.Units.Defs

namespace Ideal

variable [RingOps α] [RingOps β] [IsRing α] [IsRing β]

-- the kernel of a ring homomorphism is always an ideal
def kernel (f: α →+* β) : Ideal α where
  carrier := Set.preimage {0} f
  mem_zero' := resp_zero _
  mem_neg' := by
    intro a ha
    rw [Set.mem_preimage, resp_neg, ha, neg_zero]; rfl
  mem_add' := by
    intro a b ha hb
    rw [Set.mem_preimage, resp_add, ha, hb, add_zero]; rfl
  mem_mul_left' := by
    intro a b hb
    rw [Set.mem_preimage, resp_mul, hb, mul_zero]; rfl
  mem_mul_right' := by
    intro a b hb
    rw [Set.mem_preimage, resp_mul, hb, zero_mul]; rfl

-- if an ideal contains any units, then it must be the universal ideal
def eq_univ_of_mem_unit (i: Ideal α) (u: Units α) : u.val ∈ i.carrier -> i = .univ α := by
  intro h
  ext r
  apply Iff.intro
  intro h; trivial
  intro h; clear h
  have : u.val * (u.inv * r) ∈ i := by
    apply mem_mul_right
    assumption
  rw [←mul_assoc, u.val_mul_inv, one_mul] at this
  assumption

end Ideal
