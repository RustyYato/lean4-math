import Math.Algebra.Hom.Defs
import Math.Algebra.SetLike.Defs

variable {F R α β: Type*} [FunLike F α β]

section

namespace SubZero

variable [Zero α] [Zero β] [IsZeroHom F α β]

def image (s: SubZero α) (f: F) : SubZero β where
  carrier := s.carrier.image f
  mem_zero := ⟨0, by
    apply And.intro
    apply mem_zero s
    rw [map_zero]⟩

def preimage (s: SubZero β) (f: F) : SubZero α where
  carrier := s.carrier.preimage f
  mem_zero := by show f 0 ∈ s; rw [map_zero]; apply mem_zero

def range (f: F) : SubZero β := (image .univ f).copy (Set.range f) (by symm; apply Set.range_eq_image)

end SubZero

namespace SubOne

variable [One α] [One β] [IsOneHom F α β]

def image (s: SubOne α) (f: F) : SubOne β where
  carrier := s.carrier.image f
  mem_one := ⟨1, by
    apply And.intro
    apply mem_one s
    rw [map_one]⟩

def preimage (s: SubOne β) (f: F) : SubOne α where
  carrier := s.carrier.preimage f
  mem_one := by show f 1 ∈ s; rw [map_one]; apply mem_one

def range (f: F) : SubOne β := (image .univ f).copy (Set.range f) (by symm; apply Set.range_eq_image)

end SubOne

namespace AddSubsemigroup

variable [Add α] [Add β] [IsAddHom F α β]

def image (s: AddSubsemigroup α) (f: F) : AddSubsemigroup β where
  carrier := s.carrier.image f
  mem_add | ⟨a, ha, _⟩, ⟨b, hb, _⟩ => ⟨a + b, by
    apply And.intro
    apply mem_add s
    assumption
    assumption
    rw [map_add]; congr⟩

def preimage (s: AddSubsemigroup β) (f: F) : AddSubsemigroup α where
  carrier := s.carrier.preimage f
  mem_add {a b} ha hb := by show f _ ∈ s; rw [map_add]; apply mem_add <;> assumption

def range (f: F) : AddSubsemigroup β := (image .univ f).copy (Set.range f) (by symm; apply Set.range_eq_image)

end AddSubsemigroup

namespace Subsemigroup

variable [Mul α] [Mul β] [IsMulHom F α β]

def image (s: Subsemigroup α) (f: F) : Subsemigroup β where
  carrier := s.carrier.image f
  mem_mul | ⟨a, ha, _⟩, ⟨b, hb, _⟩ => ⟨a * b, by
    apply And.intro
    apply mem_mul s
    assumption
    assumption
    rw [map_mul]; congr⟩

def preimage (s: Subsemigroup β) (f: F) : Subsemigroup α where
  carrier := s.carrier.preimage f
  mem_mul {a b} ha hb := by show f _ ∈ s; rw [map_mul]; apply mem_mul <;> assumption

def range (f: F) : Subsemigroup β := (image .univ f).copy (Set.range f) (by symm; apply Set.range_eq_image)

end Subsemigroup

namespace SubMulAction

variable [SMul R α] [SMul R β] [IsSMulHom F R α β]

def image (s: SubMulAction R α) (f: F) : SubMulAction R β where
  carrier := s.carrier.image f
  mem_smul | r,  ⟨a, ha, _⟩ => ⟨r • a, by
    apply And.intro
    apply mem_smul s
    assumption
    rw [map_smul]; congr⟩

def preimage (s: SubMulAction R β) (f: F) : SubMulAction R α where
  carrier := s.carrier.preimage f
  mem_smul r {a} ha := by show f _ ∈ s; rw [map_smul]; apply mem_smul <;> assumption

def range (f: F) : SubMulAction R β := (image .univ f).copy (Set.range f) (by symm; apply Set.range_eq_image)

end SubMulAction

end
