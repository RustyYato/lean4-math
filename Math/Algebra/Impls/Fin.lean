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
    rw [Int.ofNat_sub, Int.ofNat_sub, Int.toNat_of_nonneg]
    rw [Int.sub_emod]
    simp [Int.negSucc_emod, Int.add_emod, Int.emod_emod, Int.neg_emod]
    conv => { rhs; rw [Int.sub_emod] }
    rw [←Int.sub_emod,  Int.ofNat_sub]
    conv => { rhs; rw [sub_sub, add_sub_assoc, Int.ofNat_add, natCast_one, add_sub_cancel] }
    rw [sub_sub, Int.add_assoc, add_sub_assoc, add_sub_cancel]
    simp [add_comm]
    any_goals
      apply Nat.le_of_lt
      refine Nat.mod_lt _ ?_
      exact Nat.zero_lt_succ n
    refine Int.emod_nonneg (Int.negSucc x) ?_
    omega
    apply Int.ofNat_le.mp
    rw [Int.toNat_of_nonneg]
    apply Int.le_of_lt
    refine Int.emod_lt_of_pos _ ?_
    omega
    refine Int.emod_nonneg (Int.negSucc x) ?_
    omega

instance : IsSemiring (Fin (n + 1)) where
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
    cases n
    · match a with
      | 0 => rfl
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
