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

variable [FunLike F α β]

variable [FieldOps β] [IsField β]
  [IsZeroHom F α β] [IsOneHom F α β]
  [IsAddHom F α β] [IsMulHom F α β]

namespace Subfield

def preimage (f: F) (s: Subfield β) : Subfield α := {
  s.toSubgroupWithZero.preimage f, s.toAddSubgroup.preimage f with
}

def image (f: F) (s: Subfield α) : Subfield β := {
  s.toSubgroupWithZero.image f, s.toAddSubgroup.image f with
}

def range (f: F) : Subfield β := {
  SubgroupWithZero.range f, AddSubgroupWithOne.range f with
}

end Subfield

namespace Subfield

variable [FieldOps β] [IsField β]

def bij_range (f: α →+* β) : α ⇔+* range f where
  toBijection := Bijection.range ⟨f, field_hom_inj f⟩
  map_zero := by
    apply Subtype.val_inj
    apply map_zero f
  map_one := by
    apply Subtype.val_inj
    apply map_one f
  map_add {_ _} := by
    apply Subtype.val_inj
    apply map_add f
  map_mul {_ _} := by
    apply Subtype.val_inj
    apply map_mul f

noncomputable def equiv_range (f: α →+* β) : α ≃+* range f := {
  (bij_range f).toEquiv, bij_range f with
}

def equiv_of_eq (a b: Subfield α) (eq: a = b) : a ≃+* b where
  toFun a := ⟨a.val, eq ▸ a.property⟩
  invFun a := ⟨a.val, eq ▸ a.property⟩
  leftInv x := rfl
  rightInv x := rfl
  map_zero := rfl
  map_one := rfl
  map_add := rfl
  map_mul := rfl

end Subfield
