import Math.Algebra.Basic
import Math.Algebra.Group.Units.Defs
import Math.Algebra.Semiring.Char
import Math.Data.Nat.Gcd

instance : One (Fin (n + 1)) := ⟨1⟩

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
  intCast m := ⟨(m % (n + 1)).toNat, by
    apply Int.ofNat_lt.mp
    rw [Int.toNat_of_nonneg]
    refine Int.emod_lt_of_pos m ?_
    omega
    refine Int.emod_nonneg m ?_
    omega⟩

instance : IsAddCommMagma (Fin (n + 1)) where
  add_comm := by
    intro a b
    show ⟨_, _⟩ = Fin.mk _ _
    simp [Nat.add_comm]

instance : IsAddGroup (Fin (n + 1)) where
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
  sub_eq_add_neg := by
    intro a b
    show Fin.mk _ _ = Fin.mk _ _
    simp
    rw [Nat.add_comm]
  zsmul_ofNat _ _ := rfl
  zsmul_negSucc _ _ := rfl
  neg_add_cancel := by
    intro a
    show Fin.mk _ _ = Fin.mk _ _
    simp
  zero_nsmul _ := by
    show Fin.mk _ _ = Fin.mk _ _
    simp
  succ_nsmul := by
    intro m a
    show Fin.mk _ _ = Fin.mk _ _
    simp
    rw [Nat.add_mul, Nat.one_mul]

instance : IsAddGroupWithOne (Fin (n + 1)) where
  natCast_zero := rfl
  natCast_succ := by
    intro a
    show Fin.mk _ _ = Fin.mk _ _
    simp
  ofNat_eq_natCast _ := rfl
  intCast_ofNat _ := rfl
  intCast_negSucc x := by
    apply neg_inj.mp
    show Fin.mk _ _ = Fin.mk _ _
    apply Fin.val_inj.mp
    apply Int.ofNat_inj.mp
    simp
    rw [Int.negSucc_emod, Int.add_sub_cancel, Int.ofNat_sub]
    rw [Int.toNat_of_nonneg, Int.sub_emod, Int.sub_emod n (_ % _),
      Int.emod_emod, ←Int.sub_emod n, ←Int.sub_emod]
    rw [Int.ofNat_sub, Int.ofNat_emod, Int.ofNat_sub, Int.ofNat_emod]
    norm_cast
    conv => {
      rhs
      rw [Int.sub_emod, Int.emod_emod, Int.sub_emod (n + 1: ℕ),
        Int.ofNat_emod, Int.emod_emod]
      rw (occs := [2]) [←Int.sub_emod]
      rw [←Int.sub_emod, Int.ofNat_succ, Int.ofNat_succ]
    }
    rw [Int.add_comm x 1, ←Int.sub_sub, Int.add_sub_cancel]
    rfl
    any_goals
      apply Nat.le_of_lt
      apply Nat.mod_lt
      apply Nat.zero_lt_succ
    refine Int.sub_nonneg_of_le ?_
    apply Int.le_of_lt_add_one
    apply Int.emod_lt
    omega
    apply Int.ofNat_le.mp
    rw [Int.toNat_of_nonneg]
    refine Int.sub_left_le_of_le_add ?_
    rw [Int.ofNat_add]
    erw [show (x: ℤ) % (n + ((1: ℕ): ℤ)) + (↑n + 1) = n + (↑x % (↑n + 1) + ↑1) by ac_rfl]
    show (n: ℤ) ≤ (n: ℤ) + _
    apply Int.le_add_of_nonneg_right
    rw [←Int.ofNat_one, ←Int.ofNat_add, ←Int.ofNat_emod, ←Int.ofNat_add]
    apply Int.ofNat_zero_le
    apply Int.le_sub_left_of_add_le
    rw [add_zero]
    apply Int.le_of_lt_add_one
    apply Int.emod_lt
    omega
    omega

instance : IsSemiring (Fin (n + 1)) where
  mul_assoc := by
    intro a b c
    show Fin.mk _ _ = Fin.mk _ _
    simp
    rw [Nat.mul_assoc, Nat.mul_mod]
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
    cases n
    · match a with
      | 0 => rfl
    rw [Nat.mod_eq_of_lt (a := _)]
    apply a.isLt
  left_distrib := by
    intro _ _ _
    show Fin.mk _ _ = Fin.mk _ _
    simp
    rw [mul_add]
  right_distrib := by
    intro _ _ _
    show Fin.mk _ _ = Fin.mk _ _
    simp
    rw [Nat.add_mul]
  npow_zero _ := rfl
  npow_succ := by
    intro a m
    show Fin.mk _ _ = Fin.mk _ _
    simp
    rw [Nat.pow_succ]

instance : IsRing (Fin (n + 1)) := inferInstance

instance : IsCommMagma (Fin (n + 1)) where
  mul_comm := by
    intro a b
    show Fin.mk _ _ = Fin.mk _ _
    simp [Nat.mul_comm]

instance : HasChar (Fin (n + 1)) (n + 1) := by
  cases n
  simp; infer_instance
  apply HasChar.of_natCast_eq_zero
  show Fin.mk _ _ = Fin.mk _ _
  simp
  intro m meq
  exact Nat.dvd_of_mod_eq_zero (Fin.mk.inj meq)

unseal Nat.xgcdAux in def Fin.toUnit (x: Fin (n + 1)) (coprime: Nat.gcd x.val (n+1) = 1 := by decide) : Units (Fin (n + 1)) :=
  have eq_one : 0 < n -> 1 = ↑x.val * x.val.gcdA (n + 1) % (↑n + 1) := by
    intro h
    replace coprime: x.val.gcd (n+1) = 1 := coprime
    have := Nat.gcd_eq_gcd_ab x.val (n+1)
    rw [coprime, natCast_one] at this
    match n with
    | 0 =>  contradiction
    | n + 1 =>
    have : 1 = (↑↑x * x.val.gcdA (n + 1 + 1) + ↑(n + 1 + 1) * x.val.gcdB (n + 1 + 1)) % (n + 1 + 1: Nat) := by
      rw [←this]
      rfl
    rw [Int.add_emod, Int.mul_emod_right, Int.add_zero, Int.emod_emod] at this
    assumption
  {
    val := x
    inv := ⟨((x.val.gcdA (n + 1)) % (n + 1)).toNat, by
      apply (Int.toNat_lt _).mpr
      apply Int.emod_lt_of_pos
      omega
      apply Int.emod_nonneg
      omega⟩
    val_mul_inv := by
      cases n with
      | zero => apply Subsingleton.allEq
      | succ n =>
      apply Fin.val_inj.mp
      apply Int.ofNat_inj.mp
      show _ = ((1 % (n + 2)): Int)
      simp [Fin.val_mul]
      rw [Int.max_eq_left, Int.mul_emod, Int.emod_emod, ←Int.mul_emod]
      symm
      apply eq_one
      apply Nat.zero_lt_succ
      apply Int.emod_nonneg
      omega
    inv_mul_val := by
      cases n with
      | zero => apply Subsingleton.allEq
      | succ n =>
      rw [Fin.mul_comm]
      apply Fin.val_inj.mp
      apply Int.ofNat_inj.mp
      show _ = ((1 % (n + 2)): Int)
      simp [Fin.val_mul]
      rw [Int.max_eq_left, Int.mul_emod, Int.emod_emod, ←Int.mul_emod]
      symm
      apply eq_one
      apply Nat.zero_lt_succ
      apply Int.emod_nonneg
      omega
  }
