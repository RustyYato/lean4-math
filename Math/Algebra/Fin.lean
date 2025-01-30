import Math.Algebra.Basic

instance : One (Fin (n + 2)) := ⟨1⟩

instance : SMul ℕ (Fin n) where
  smul m x := ⟨(m * x) % n, Nat.mod_lt _ x.pos⟩
instance : Pow (Fin n) ℕ where
  pow x m := ⟨(x ^ m) % n, Nat.mod_lt _ x.pos⟩

instance : Neg (Fin n) where
  neg x := ⟨0, x.pos⟩  - x

instance : SMul ℤ (Fin (n + 1)) where
  smul := zsmulRec

instance : NatCast (Fin (n + 1)) where
  natCast m := ⟨m % (n + 1), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩
instance : IntCast (Fin (n + 1)) where
  intCast := intCastRec

instance : IsSemiring (Fin (n + 2)) where
  add_comm := by
    intro a b
    show ⟨_, _⟩ = Fin.mk _ _
    simp [Nat.add_comm]
  add_assoc := by
    intro a b c
    show ⟨_, _⟩ = Fin.mk _ _
    simp [Nat.add_assoc]
  zero_add := by
    intro a
    simp
  add_zero := by
    intro a
    simp
  natCast_zero := rfl
  natCast_succ := by
    intro a
    show Fin.mk _ _ = Fin.mk _ _
    simp
  ofNat_eq_natCast _ := rfl
  mul_assoc := by
    intro a b c
    show Fin.mk _ _ = Fin.mk _ _
    simp
    rw [Nat.mul_assoc,
      Nat.mul_mod]
    congr
    rw [Nat.mod_eq_of_lt]
    exact a.isLt
  zero_mul := by
    intro
    show Fin.mk _ _ = Fin.mk _ _
    simp
  mul_zero := by
    intro
    show Fin.mk _ _ = Fin.mk _ _
    simp
  one_mul := by
    intro a
    show Fin.mk _ _ = Fin.mk _ _
    simp
    congr; rw [Nat.mod_eq_of_lt a.isLt]
  mul_one := by
    intro a
    show Fin.mk _ _ = Fin.mk _ _
    simp
    congr
    rw [Nat.mod_eq_of_lt (a := 1), Nat.mul_one, Nat.mod_eq_of_lt a.isLt]
    simp
  left_distrib := by
    intro _ _ _
    show Fin.mk _ _ = Fin.mk _ _
    simp
    rw [Nat.mul_mod, Nat.mod_mod, ←Nat.mul_mod, Nat.mul_add]
  right_distrib := by
    intro _ _ _
    show Fin.mk _ _ = Fin.mk _ _
    simp
    rw [Nat.add_mul]
  zero_nsmul _ := by
    show Fin.mk _ _ = Fin.mk _ _
    simp
  succ_nsmul := by
    intro m a
    show Fin.mk _ _ = Fin.mk _ _
    simp
    rw [Nat.add_mul, Nat.one_mul]
  npow_zero _ := rfl
  npow_succ := by
    intro a m
    show Fin.mk _ _ = Fin.mk _ _
    simp
    rw [Nat.pow_succ]

instance : IsRing (Fin (n + 2)) where
  zsmul_ofNat _ _ := rfl
  zsmul_negSucc _ _ := rfl
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl
  sub_eq_add_neg := by
    intro a b
    show Fin.mk _ _ = Fin.mk _ _
    simp
    rw [Nat.add_comm]
  neg_add_cancel := by
    intro a
    show Fin.mk _ _ = Fin.mk _ _
    simp

instance : IsCommMagma (Fin (n + 2)) where
  mul_comm := by
    intro a b
    show Fin.mk _ _ = Fin.mk _ _
    simp [Nat.mul_comm]

def Fin.char_eq : char (Fin (n + 2)) = n + 2 := by
  apply char_eq_of_natCast_eq_zero
  show Fin.mk _ _ = Fin.mk _ _
  simp
  intro m meq
  exact Nat.dvd_of_mod_eq_zero (Fin.mk.inj meq)
