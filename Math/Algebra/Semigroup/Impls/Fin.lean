import Math.Algebra.Semigroup.Defs

variable (n: ℕ) [NeZero n]

instance : IsAddSemigroup (Fin n) where
  add_assoc := by
    intro a b c
    show ⟨_, _⟩ = Fin.mk _ _
    simp [Nat.add_assoc]

instance : IsSemigroup (Fin n) where
  mul_assoc := by
    intro a b c
    show Fin.mk _ _ = Fin.mk _ _
    simp only [Nat.mod_mul_mod, Fin.mk.injEq]
    rw [Nat.mul_mod a, Nat.mod_mod, ←Nat.mul_mod, Nat.mul_assoc]

instance : IsAddCommMagma (Fin n) where
  add_comm := by
    intro a b
    show ⟨_, _⟩ = Fin.mk _ _
    simp [Nat.add_comm]

instance : IsCommMagma (Fin n) where
  mul_comm := by
    intro a b
    show ⟨_, _⟩ = Fin.mk _ _
    simp [Nat.mul_comm]

instance : IsAddZeroClass (Fin n) where
  zero_add := by
    intro a
    simp
  add_zero := by
    intro a
    simp

instance : IsMulOneClass (Fin n) := by
  apply IsMulOneClass.ofCommMagma
  intro a
  show Fin.mk _ _ = Fin.mk _ _
  simp
  congr; rw [Nat.mod_eq_of_lt a.isLt]

instance : IsMulZeroClass (Fin n) := by
  apply IsMulZeroClass.ofCommMagma
  intro a
  show Fin.mk _ _ = Fin.mk _ _
  simp
