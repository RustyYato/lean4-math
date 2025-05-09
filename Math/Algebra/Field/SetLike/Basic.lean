import Math.Algebra.Field.SetLike.Defs
import Math.Algebra.GroupWithZero.SetLike.Basic
import Math.Algebra.Ring.SetLike.Basic
import Math.Algebra.GroupWithZero.Hom
import Math.Algebra.Field.Hom
import Math.Algebra.Field.SetLike.Lattice

variable [SetLike S α] [FieldOps α] [IsField α] [IsSubfield S] (s: S)

instance : FieldOps s := inferInstance
instance : IsField s := inferInstance

instance (s: Subfield α) : FieldOps s := inferInstance
instance (s: Subfield α) : IsField s := inferInstance
instance (s: Subfield α) : IsRing s := inferInstance
instance (s: Subfield α) : IsSemiring s := inferInstance

namespace Subfield

variable [FieldOps β] [IsField β]

def preimage (f: α →+* β) (s: Subfield β) : Subfield α where
  carrier := s.carrier.preimage f
  mem_zero := by
    show f 0 ∈ s
    rw [map_zero]
    apply mem_zero
  mem_one := by
    show f 1 ∈ s
    rw [map_one]
    apply mem_one
  mem_add := by
    intro a b ha hb
    show f (a + b) ∈ s
    rw [map_add]
    apply mem_add
    assumption
    assumption
  mem_mul := by
    intro a b ha hb
    show f (a * b) ∈ s
    rw [map_mul]
    apply mem_mul
    assumption
    assumption
  mem_neg := by
    intro a ha
    show f (-a) ∈ s
    rw [map_neg]
    apply mem_neg
    assumption
  mem_inv? := by
    intro a h ha
    show f (a⁻¹?) ∈ s
    rw [map_inv?]
    apply mem_inv?
    assumption

def image (f: α →+* β) (s: Subfield α) : Subfield β where
  carrier := s.carrier.image f
  mem_zero := by
    exists 0
    apply And.intro
    apply mem_zero s
    rw [map_zero]
  mem_one := by
    exists 1
    apply And.intro
    apply mem_one s
    rw [map_one]
  mem_add := by
    rintro a b ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exists a + b
    apply And.intro
    apply mem_add s
    assumption
    assumption
    rw [map_add]
  mem_mul := by
    rintro a b ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exists a * b
    apply And.intro
    apply mem_mul s
    assumption
    assumption
    rw [map_mul]
  mem_neg := by
    rintro a ⟨a, ha, rfl⟩
    exists -a
    apply And.intro
    apply mem_neg s
    assumption
    rw [map_neg]
  mem_inv? := by
    rintro a fanez ⟨a, ha, rfl⟩
    rw [←map_zero f] at fanez
    have : a ≠ 0 := by
      rintro rfl
      contradiction
    exists a⁻¹?
    apply And.intro
    apply mem_inv? s
    assumption
    rw [map_inv?]

def range (f: α →+* β) : Subfield β :=
  (Subfield.image f ⊤).copy (Set.range f) <| by
    rw [image, Set.range_eq_image]
    rfl

noncomputable def equiv_range (f: α →+* β) : α ≃+* range f where
  toFun a := ⟨f a, Set.mem_range'⟩
  invFun a := Classical.choose a.property
  leftInv x := by
    simp
    apply field_hom_inj f
    have : ∃a, f x = f a := ⟨x, rfl⟩
    exact (Classical.choose_spec this).symm
  rightInv x := by
    simp; congr
    exact (Classical.choose_spec x.property).symm
  map_zero := by simp [map_zero]; rfl
  map_one := by simp [map_one]; rfl
  map_add {_ _} := by simp [map_add]; rfl
  map_mul {_ _} := by simp [map_mul]; rfl

noncomputable def equiv_of_eq (a b: Subfield α) (eq: a = b) : a ≃+* b where
  toFun a := ⟨a.val, eq ▸ a.property⟩
  invFun a := ⟨a.val, eq ▸ a.property⟩
  leftInv x := rfl
  rightInv x := rfl
  map_zero := rfl
  map_one := rfl
  map_add := rfl
  map_mul := rfl

end Subfield
