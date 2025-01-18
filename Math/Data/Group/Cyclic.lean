import Math.Data.Group.Basic

instance {n m: Nat} [NeZero n] [NeZero m] : NeZero (n * m) where
  out := by
    intro h
    cases Nat.mul_eq_zero.mp h <;> (rename_i h; exact NeZero.ne _ h)

def fin_inverse (x: Fin n): Fin n :=
  Fin.mk ((n - x.val) % n) (Nat.mod_lt _ (Nat.zero_lt_of_ne_zero (by
    intro h
    cases h
    exact x.elim0)))

namespace Group

-- a cyclic group with n elements
def NatAddMod (n: Nat) [NeZero n] : Group where
  ty := Fin n
  one' := ⟨0, Nat.zero_lt_of_ne_zero (NeZero.ne _)⟩
  mul' a b := a + b
  inv' := fin_inverse
  one_mul' x := by
    apply Fin.val_inj.mp
    show ((0: Nat) + x.val) % _ = x.val
    rw [Nat.zero_add, Nat.mod_eq_of_lt x.isLt]
  mul_assoc' := by
    intro a b c
    simp [Fin.add_def]
    rw [Nat.add_assoc]
  inv_mul' := by
    intro a
    simp [Fin.add_def, fin_inverse]

def IsoClass.Cyclic (n: Nat) [NeZero n] := ⟦NatAddMod n⟧

instance : Subsingleton (NatAddMod 1).ty :=
  inferInstanceAs (Subsingleton (Fin 1))

def cyclic_one_eq_trivial : IsoClass.Cyclic 1 = 1 := by
  apply Quotient.sound
  apply eq_trivial_of_subsingleton

end Group
