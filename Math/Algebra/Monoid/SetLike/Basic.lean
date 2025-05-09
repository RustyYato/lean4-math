import Math.Algebra.Monoid.SetLike.Lattice
import Math.Algebra.Semigroup.SetLike.Basic
import Math.Algebra.SetLike.Hom
import Math.Algebra.Monoid.Defs
import Math.Algebra.Monoid.Hom

def mem_npow
  [SetLike S α] [MonoidOps α] [IsSubmonoid S] [IsMonoid α]
  (s: S) {a: α} (n: ℕ) (h: a ∈ s) : a ^ n ∈ s := by
  induction n with
  | zero =>
    rw [npow_zero]
    apply mem_one
  | succ n ih =>
    rw [npow_succ]
    apply mem_mul
    assumption
    assumption

def mem_nsmul
  [SetLike S α] [AddMonoidOps α] [IsAddSubmonoid S] [IsAddMonoid α]
  (s: S) {a: α} (n: ℕ) (h: a ∈ s) : n • a ∈ s :=
  mem_npow (S := MulOfAdd S) s n h

variable [SetLike S α]

section

variable [Mul α] [One α] [Add α] [Zero α] [IsOneMem S] [IsZeroMem S] [IsAddMem S] [IsMulMem S] (s: S)

instance : One s where
  one := ⟨1, mem_one _⟩

instance : Zero s where
  zero := ⟨0, mem_zero _⟩

@[simp]
def zero_val : (0: s).val = 0 := rfl

@[simp]
def one_val : (1: s).val = 1 := rfl

instance [IsMulOneClass α] : IsMulOneClass s where
  one_mul a := by
    apply Subtype.val_inj
    apply one_mul
  mul_one a := by
    apply Subtype.val_inj
    apply mul_one

instance [IsMulZeroClass α] : IsMulZeroClass s where
  zero_mul a := by
    apply Subtype.val_inj
    apply zero_mul
  mul_zero a := by
    apply Subtype.val_inj
    apply mul_zero

instance [IsAddZeroClass α] : IsAddZeroClass s where
  zero_add a := by
    apply Subtype.val_inj
    apply zero_add
  add_zero a := by
    apply Subtype.val_inj
    apply add_zero

instance [IsMulOneClass α] (s: Submonoid α) : IsMulOneClass s := inferInstance
instance [IsAddZeroClass α] (s: AddSubmonoid α) : IsAddZeroClass s := inferInstance

end

section

variable [MonoidOps α] [IsMonoid α] [IsSubmonoid S] [AddMonoidOps α] [IsAddMonoid α] [IsAddSubmonoid S] (s: S)

instance : Pow s ℕ  where
  pow a n := ⟨a.val ^ n, mem_npow _ _ a.property⟩

instance : SMul ℕ s  where
  smul n a := ⟨n • a.val, mem_nsmul _ _ a.property⟩

instance : IsMonoid s where
  npow_zero _ := by
    apply Subtype.val_inj
    apply npow_zero
  npow_succ _ _ := by
    apply Subtype.val_inj
    apply npow_succ

instance : IsAddMonoid s where
  zero_nsmul _ := by
    apply Subtype.val_inj
    apply zero_nsmul
  succ_nsmul _ _ := by
    apply Subtype.val_inj
    apply succ_nsmul

instance (s: Submonoid α) : IsMonoid s := inferInstance
instance (s: AddSubmonoid α) : IsAddMonoid s := inferInstance

@[simp]
def nsmul_val (n: ℕ) (a: s) : (n • a).val = n • a.val := rfl

@[simp]
def npow_val (n: ℕ) (a: s) : (a ^ n).val = a.val ^ n := rfl

def AddGroupEmbedding.subtypeVal : s ↪+ α := {
    toEmbedding := Embedding.subtypeVal
    map_zero := rfl
    map_add := rfl
  }

def GroupEmbedding.subtypeVal : s ↪* α := {
    toEmbedding := Embedding.subtypeVal
    map_one := rfl
    map_mul := rfl
  }

def AddGroupHom.subtypeVal : s →+ α := (AddGroupEmbedding.subtypeVal s).toAddGroupHom

def GroupHom.subtypeVal : s →* α := (GroupEmbedding.subtypeVal s).toGroupHom

end

namespace Submonoid

variable {F α β: Type*} [FunLike F α β]
  [MonoidOps α] [MonoidOps β]
  [IsMonoid α] [IsMonoid β]
  [IsOneHom F α β] [IsMulHom F α β]

def image (s: Submonoid α) (f: F) : Submonoid β := {
  s.toSubsemigroup.image f, s.toSubOne.image f with
}

def preimage (s: Submonoid β) (f: F) : Submonoid α := {
  s.toSubsemigroup.preimage f, s.toSubOne.preimage f with
}

def range (f: F) : Submonoid β := (image ⊤ f).copy (Set.range f) (by symm; apply Set.range_eq_image)

end Submonoid

namespace AddSubmonoid

variable {F α β: Type*} [FunLike F α β]
  [AddMonoidOps α] [AddMonoidOps β]
  [IsAddMonoid α] [IsAddMonoid β]
  [IsZeroHom F α β] [IsAddHom F α β]

def image (s: AddSubmonoid α) (f: F) : AddSubmonoid β := {
  s.toAddSubsemigroup.image f, s.toSubZero.image f with
}

def preimage (s: AddSubmonoid β) (f: F) : AddSubmonoid α := {
  s.toAddSubsemigroup.preimage f, s.toSubZero.preimage f with
}

def range (f: F) : AddSubmonoid β := (image ⊤ f).copy (Set.range f) (by symm; apply Set.range_eq_image)

end AddSubmonoid
