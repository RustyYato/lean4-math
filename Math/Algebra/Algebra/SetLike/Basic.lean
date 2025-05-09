import Math.Algebra.Algebra.SetLike.Defs
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

variable [SetLike S α] [SemiringOps R] [IsSemiring R] [SemiringOps α] [IsSemiring α]
  [AlgebraMap R α] [SMul R α] [IsAlgebra R α] [IsSubalgebra S R]

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
