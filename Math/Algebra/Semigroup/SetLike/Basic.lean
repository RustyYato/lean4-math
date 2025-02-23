import Math.Algebra.Semigroup.SetLike.Defs
import Math.Algebra.Semigroup.Defs

variable [SetLike S α] [Mul α] [IsMulMem S] [Add α] [IsAddMem S] (s: S)

instance : Mul s where
  mul a b := ⟨a.val * b.val, mem_mul _ a.property b.property⟩

instance [IsSemigroup α] : IsSemigroup s where
  mul_assoc a b c := by
    apply Subtype.val_inj
    apply mul_assoc

instance [IsCommMagma α] : IsCommMagma s where
  mul_comm a b := by
    apply Subtype.val_inj
    apply mul_comm

instance : Add s where
  add a b := ⟨a.val + b.val, mem_add _ a.property b.property⟩

instance [IsAddSemigroup α] : IsAddSemigroup s where
  add_assoc a b c := by
    apply Subtype.val_inj
    apply add_assoc

instance [IsAddCommMagma α] : IsAddCommMagma s where
  add_comm a b := by
    apply Subtype.val_inj
    apply add_comm

instance [IsSemigroup α] (s: Subsemigroup α) : IsSemigroup s := inferInstance
instance [IsCommMagma α] (s: Subsemigroup α) : IsCommMagma s := inferInstance

instance [IsAddSemigroup α] (s: AddSubsemigroup α) : IsAddSemigroup s := inferInstance
instance [IsAddCommMagma α] (s: AddSubsemigroup α) : IsAddCommMagma s := inferInstance
