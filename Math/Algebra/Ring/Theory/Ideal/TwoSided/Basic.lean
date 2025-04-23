import Math.Algebra.Ring.Theory.Ideal.Defs
import Math.Algebra.Hom.Defs
import Math.Algebra.Group.Hom
import Math.Algebra.Monoid.Units.Defs

namespace Ideal

variable [RingOps α] [RingOps β] [IsRing α] [IsRing β]

-- the preimage of a ring homomorphism is always an ideal
def preimage (f: α →+* β) (i: Ideal β) : Ideal α where
  carrier := Set.preimage i.carrier f
  mem_zero := by
    show f 0 ∈ i
    erw [map_zero]
    apply mem_zero
  mem_neg := by
    intro a ha
    show f _ ∈ i
    rw [map_neg]
    apply mem_neg
    assumption
  mem_add := by
    intro a b ha hb
    show f (a + b) ∈ i
    rw [map_add]
    apply mem_add
    assumption
    assumption
  mem_mul_left := by
    intro a b hb
    show f _ ∈ i
    rw [map_mul]
    apply mem_mul_left
    assumption
  mem_mul_right := by
    intro a b hb
    show f _ ∈ i
    rw [map_mul]
    apply mem_mul_right
    assumption

def image (f: α →+* β) (i: Ideal α) (h: Function.Surjective f) : Ideal β where
  carrier := Set.image f i.carrier
  mem_zero := by
    rw [←map_zero f]
    apply Set.mem_image'
    apply mem_zero i
  mem_add {a b} ha hb := by
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    rw [←map_add]
    apply Set.mem_image'
    apply mem_add i
    assumption
    assumption
  mem_neg {a} ha := by
    obtain ⟨a, ha, rfl⟩ := ha
    rw [←map_neg]
    apply Set.mem_image'
    apply mem_neg i
    assumption
  mem_mul_left := by
    rintro r _ ⟨x, hx, rfl⟩
    obtain ⟨r, rfl⟩ := h r
    rw [←map_mul]
    apply Set.mem_image'
    apply mem_mul_left i
    assumption
  mem_mul_right := by
    rintro r _ ⟨x, hx, rfl⟩
    obtain ⟨r, rfl⟩ := h r
    rw [←map_mul]
    apply Set.mem_image'
    apply mem_mul_right i
    assumption

def range (f: α →+* β) (h: Function.Surjective f) : Ideal β where
  carrier := Set.range f
  mem_zero := by
    rw [←map_zero f]
    apply Set.mem_range'
  mem_add {a b} ha hb := by
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    rw [←map_add]
    apply Set.mem_range'
  mem_neg {a} ha := by
    obtain ⟨a, ha, rfl⟩ := ha
    rw [←map_neg]
    apply Set.mem_range'
  mem_mul_left := by
    rintro r _ ⟨x, hx, rfl⟩
    obtain ⟨r, rfl⟩ := h r
    rw [←map_mul]
    apply Set.mem_range'
  mem_mul_right := by
    rintro r _ ⟨x, hx, rfl⟩
    obtain ⟨r, rfl⟩ := h r
    rw [←map_mul]
    apply Set.mem_range'

-- the kernel is the preimage of the 0 ideal
def kernel (f: α →+* β) : Ideal α := preimage f 0

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
