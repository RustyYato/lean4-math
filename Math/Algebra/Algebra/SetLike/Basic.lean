import Math.Algebra.Algebra.SetLike.Lattice
import Math.Algebra.Ring.SetLike.Basic
import Math.Algebra.Monoid.Action.SetLike.Basic
import Math.Algebra.Algebra.Defs

instance [RingOps R] [IsRing R] [RingOps α] [IsRing α] [AlgebraMap R α] : IsSubring (Subalgebra R α) where
  mem_neg s a ha := by
    rw [←neg_one_mul, ←map_one (algebraMap (R := R)),
      ←map_neg]
    apply mem_mul
    apply mem_algebraMap
    assumption

variable [SetLike S α]
  [SemiringOps R] [IsSemiring R]
  [SemiringOps α] [IsSemiring α] [AlgebraMap R α] [SMul R α] [IsAlgebra R α]
  [SemiringOps β] [IsSemiring β] [AlgebraMap R β] [SMul R β] [IsAlgebra R β]
  [IsSubalgebra S R]

section

variable (s: S)

instance : IsSMulMem S R where
  mem_smul s r a ha := by
    rw [smul_def]
    apply mem_mul
    apply mem_algebraMap
    assumption

instance : AlgebraMap R s where
  toFun r := ⟨algebraMap r, mem_algebraMap _ _ _⟩
  map_zero := by congr; rw [map_zero]
  map_one := by congr; rw [map_one]
  map_add {a b} := by apply Subtype.val_inj; simp [map_add]
  map_mul {a b} := by apply Subtype.val_inj; simp [map_mul]

instance : IsAlgebra R s where
  commutes r s := by
    apply Subtype.val_inj
    apply commutes
  smul_def r a := by
    apply Subtype.val_inj
    apply smul_def

end

section

variable (s: Subalgebra R α)

instance : SMul R s := inferInstance
instance : AlgebraMap R s := inferInstance
instance : IsAlgebra R s := inferInstance

end

namespace Subalgebra

def image (s: Subalgebra R α) (f: α →ₐ[R] β) : Subalgebra R β where
  carrier := s.carrier.image f
  mem_add := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    rw [←map_add]
    apply Set.mem_image'
    apply mem_add s
    assumption
    assumption
  mem_mul := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    rw [←map_mul]
    apply Set.mem_image'
    apply mem_mul s
    assumption
    assumption
  mem_algebraMap r := by
    rw [←map_algebraMap f]
    apply Set.mem_image'
    apply mem_algebraMap R s r

def range (f: α →ₐ[R] β) : Subalgebra R β := copy _ (image ⊤ f) (Set.range f) <| by symm; apply Set.range_eq_image

def preimage (s: Subalgebra R β) (f: α →ₐ[R] β) : Subalgebra R α where
  carrier := s.carrier.preimage f
  mem_add := by
    intro a b ha hb
    show f _ ∈ s; rw [map_add]; apply mem_add <;> assumption
  mem_mul := by
    intro a b ha hb
    show f _ ∈ s; rw [map_mul]; apply mem_mul <;> assumption
  mem_algebraMap r := by
    show f _ ∈ s; rw [map_algebraMap]; apply mem_algebraMap

end Subalgebra
