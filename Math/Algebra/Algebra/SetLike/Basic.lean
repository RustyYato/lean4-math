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

variable [FunLike F α β]

variable [IsAddHom F α β] [IsMulHom F α β] [IsAlgebraMapHom F R α β]

namespace Subalgebra

def preimage (f: F) (s: Subalgebra R β) : Subalgebra R α := {
  s.toAddSubsemigroup.preimage f, s.toSubsemigroup.preimage f with
  mem_algebraMap r := by
    show f _ ∈ s; rw [map_algebraMap]; apply mem_algebraMap
}

def image (f: F) (s: Subalgebra R α) : Subalgebra R β := {
  s.toAddSubsemigroup.image f, s.toSubsemigroup.image f with
  mem_algebraMap r := by
    rw [←map_algebraMap f r]
    apply Set.mem_image'
    apply mem_algebraMap R s r
}

def range (f: F) : Subalgebra R β := copy _ (image f ⊤) (Set.range f) (by symm; apply Set.range_eq_image)

end Subalgebra
