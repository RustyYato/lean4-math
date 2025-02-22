import Math.Algebra.Monoid.Char
import Math.Algebra.Field.Defs
import Math.Algebra.Semiring.Char

instance : SemiringOps Bool where
  add := xor
  mul := and
  zero := false
  one := true
  natCast n := n % 2 != 0
  ofNat n := ⟨n % 2 != 0⟩
  nsmul n x := and (n % 2 != 0) x
  npow
  | _, 0 => true
  | x, _ => x

instance : Neg Bool := ⟨id⟩

instance : RingOps Bool where
  sub := xor
  intCast n := n % 2 != 0
  ofNat n := ⟨n % 2 != 0⟩
  zsmul n x := and (n % 2 != 0) x

instance : FieldOps Bool where
  checked_pow
  | _, .ofNat 0, _ => 1
  | x, _, _ => x
  checked_div x _ _ := x
  checked_invert _ _ := true

instance : IsCommMagma Bool where
  mul_comm := by decide +kernel

instance : IsField Bool where
  add_comm := by decide +kernel
  add_assoc := by decide +kernel
  zero_add := by decide +kernel
  add_zero := by decide +kernel
  natCast_zero := by decide +kernel
  natCast_succ n := by
    show (n.succ % 2 != 0) = xor (n % 2 != 0) true
    erw [Bool.xor_true, Bool.not_not]
    rw [Nat.succ_eq_add_one, Nat.add_mod]
    cases Nat.mod_two_eq_zero_or_one n <;> rename_i h
    rw [beq_of_eq h]
    rw [bne_iff_ne]
    intro g
    rw [h] at g
    contradiction
    rw [h, beq_false_of_ne, bne_eq_false_iff_eq]
    decide
  ofNat_eq_natCast := by
    intro n
    dsimp [OfNat.ofNat, Nat.cast, NatCast.natCast]
    rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
  mul_assoc := by decide +kernel
  zero_mul := by decide +kernel
  mul_zero := by decide +kernel
  one_mul := by decide +kernel
  mul_one := by decide +kernel
  left_distrib := by decide +kernel
  right_distrib := by decide +kernel
  sub_eq_add_neg := by decide +kernel
  zsmul_negSucc := by
    intro n a
    show and _ _ = (and _ _)
    rw [Int.negSucc_emod]
    congr 1
    erw [Nat.succ_eq_add_one, ←Int.ofNat_emod, Nat.add_mod]
    cases Nat.mod_two_eq_zero_or_one n <;> (rename_i h; rw [h]; rfl)
    decide
  zsmul_ofNat := by
    intro n a
    show and _ _ = and _ _
    erw [←Int.ofNat_emod]
    cases Nat.mod_two_eq_zero_or_one n <;> (rename_i h; rw [h]; clear h)
    revert a; decide
    rfl
  neg_add_cancel := by decide +kernel
  intCast_ofNat := by
    intro n
    show (_ % 2 != 0) = (_ % 2 != 0)
    erw [←Int.ofNat_emod]
    cases Nat.mod_two_eq_zero_or_one n <;> (rename_i h; rw [h]; rfl)
  intCast_negSucc := by
    intro n
    show (_ % 2 != 0) = (_ % 2 != 0)
    erw [Int.negSucc_emod, ←Int.ofNat_emod, Nat.succ_eq_add_one, Nat.add_mod]
    cases Nat.mod_two_eq_zero_or_one n <;> (rename_i h; rw [h]; rfl)
    decide
  mul_inv?_cancel := by decide +kernel
  div?_eq_mul_inv? := by decide +kernel
  zpow?_ofNat := by
    intro n x
    cases n
    rfl
    rfl
  zpow?_negSucc := by
    intro _ b _; cases b; contradiction; rfl
  npow_zero := by decide +kernel
  npow_succ := by
    intro n a
    show a = _
    cases n
    rfl; symm
    apply Bool.and_self
  zero_nsmul := by decide +kernel
  succ_nsmul := by
    intro n a
    show and _ a = xor _ _
    cases n
    revert a; decide +kernel
    show and _ a = xor (and _ _) _
    rename_i n
    rw [Nat.add_mod]
    cases Nat.mod_two_eq_zero_or_one (n+1) <;> (rename_i h; rw [h]; cases a <;> rfl)

instance : HasChar Bool 2 := by
  apply HasChar.of_natCast_eq_zero
  rfl
  intro n h
  apply Nat.dvd_of_mod_eq_zero
  exact bne_eq_false_iff_eq.mp h
