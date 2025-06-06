import Math.Algebra.AddMonoidWithOne.SetLike.Defs
import Math.Algebra.Monoid.SetLike.Basic
import Math.Algebra.AddMonoidWithOne.Defs

variable [SetLike S α] [AddMonoidWithOneOps α] [IsAddSubmonoidWithOne S] [IsAddMonoidWithOne α]
   (s: S)

def mem_natCast (n: ℕ): (n: α) ∈ s := by
  induction n with
  | zero =>
    rw [natCast_zero]
    apply mem_zero
  | succ n ih =>
    rw [natCast_add, natCast_one]
    apply mem_add
    assumption
    apply mem_one

def mem_ofNat (n: ℕ): OfNat.ofNat (n + 2) ∈ s := by
  rw [ofNat_eq_natCast]
  apply mem_natCast

instance : NatCast s where
  natCast n := ⟨n, mem_natCast _ _⟩

instance : IsAddMonoidWithOne s where
  natCast_zero := by
    apply Subtype.val_inj
    apply natCast_zero
  natCast_succ _ := by
    apply Subtype.val_inj
    apply natCast_succ

def natRange_sub: ∀s: S, Set.range (fun n: ℕ => (n: α)) ⊆  s := by
  rintro s _ ⟨n, rfl⟩
  dsimp
  show ↑n ∈ s
  apply mem_natCast

@[simp]
def natCast_val (n: ℕ) : (n: s).val = n := rfl

variable [FunLike F α β]
   [AddMonoidWithOneOps β] [IsAddMonoidWithOne β]
   [IsZeroHom F α β] [IsOneHom F α β] [IsAddHom F α β]

namespace AddSubmonoidWithOne

def preimage (f: F) (s: AddSubmonoidWithOne β) : AddSubmonoidWithOne α := {
  s.toAddSubmonoid.preimage f, s.toSubOne.preimage f with
}

def image (f: F) (s: AddSubmonoidWithOne α) : AddSubmonoidWithOne β := {
  s.toAddSubmonoid.image f, s.toSubOne.image f with
}

def range (f: F) : AddSubmonoidWithOne β := {
  AddSubmonoid.range f, SubOne.range f with
}

end AddSubmonoidWithOne
