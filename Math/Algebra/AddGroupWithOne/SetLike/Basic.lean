import Math.Algebra.AddGroupWithOne.SetLike.Defs
import Math.Algebra.AddMonoidWithOne.SetLike.Basic
import Math.Algebra.Group.SetLike.Basic
import Math.Algebra.AddGroupWithOne.Defs

variable [SetLike S α] [AddGroupWithOneOps α] [IsAddSubgroupWithOne S] [IsAddGroupWithOne α]
   (s: S)

def mem_intCast (n: ℤ): (n: α) ∈ s := by
  induction n using Int.coe_cases with
  | ofNat n =>
    rw [intCast_ofNat]
    apply mem_natCast
  | negSucc n =>
    rw [intCast_negSucc]
    apply mem_neg
    apply mem_natCast

instance : IntCast s where
  intCast n := ⟨n, mem_intCast _ _⟩

instance : IsAddGroupWithOne s := {
  instIsAddGroupElem s, instIsAddMonoidWithOneElem s with
  intCast_ofNat n := by
    apply Subtype.val_inj
    apply intCast_ofNat
  intCast_negSucc n := by
    apply Subtype.val_inj
    apply intCast_negSucc
}

def intRange_sub: ∀s: S, Set.range (fun n: ℤ => (n: α)) ⊆  s := by
  rintro s _ ⟨n, rfl⟩
  dsimp
  show ↑n ∈ s
  apply mem_intCast

@[simp]
def intCast_val (n: ℤ) : (n: s).val = n := rfl

variable [FunLike F α β]
   [AddGroupWithOneOps β] [IsAddGroupWithOne β]
   [IsZeroHom F α β] [IsOneHom F α β] [IsAddHom F α β]

namespace AddSubgroupWithOne

def preimage (f: F) (s: AddSubgroupWithOne β) : AddSubgroupWithOne α := {
  s.toAddSubgroup.preimage f, s.toSubOne.preimage f with
}

def image (f: F) (s: AddSubgroupWithOne α) : AddSubgroupWithOne β := {
  s.toAddSubgroup.image f, s.toSubOne.image f with
}

def range (f: F) : AddSubgroupWithOne β := {
  AddSubgroup.range f, SubOne.range f with
}

end AddSubgroupWithOne
