import Math.Algebra.AddMonoidWithOne.Impls.Fin
import Math.Algebra.GroupWithZero.Defs
import Math.Algebra.Monoid.Units.Defs
import Math.Data.Nat.Gcd
import Math.Logic.Fact

instance [Fact (Nat.IsPrime n)] : NeZero n where
  out := by
    have : Nat.IsPrime n := Fact.proof
    rintro rfl
    contradiction

unseal Nat.xgcdAux in def Fin.toUnit {n: ℕ} (x: Fin n) (coprime: Nat.gcd x.val n = 1 := by decide) :
  have : NeZero n := {
    out := (Nat.ne_of_lt x.pos).symm
  }
  Units (Fin n) :=
  have ne : NeZero n := {
    out := (Nat.ne_of_lt x.pos).symm
  }
  have eq_one : 1 < n -> 1 = ↑x.val * x.val.gcdA n % n := by
    intro h
    replace coprime: x.val.gcd n = 1 := coprime
    have := Nat.gcd_eq_gcd_ab x.val n
    rw [coprime, Int.ofNat_one] at this
    match n with
    | n + 2 =>
    have : 1 = (↑↑x * x.val.gcdA (n + 2) + ↑(n + 2) * x.val.gcdB (n + 2)) % (n + 2: Nat) := by
      rw [←this]
      rfl
    rw [Int.add_emod, Int.mul_emod_right, Int.add_zero, Int.emod_emod] at this
    assumption
  {
    val := x
    inv := ⟨((x.val.gcdA n) % n).toNat, by
      have := NeZero.ne n
      apply (Int.toNat_lt _).mpr
      apply Int.emod_lt_of_pos
      omega
      apply Int.emod_nonneg
      omega⟩
    val_mul_inv := by
      match n, ne with
      | 1, _ => apply Subsingleton.allEq
      | n + 2, _ =>
      apply Fin.val_inj.mp
      apply Int.ofNat_inj.mp
      show _ = ((1 % (n + 2)): Int)
      simp [Fin.val_mul]
      rw [Int.max_eq_left, Int.mul_emod, Int.emod_emod, ←Int.mul_emod]
      symm
      apply eq_one
      apply Nat.succ_lt_succ
      apply Nat.zero_lt_succ
      apply Int.emod_nonneg
      omega
    inv_mul_val := by
      match n, ne with
      | 1, _ => apply Subsingleton.allEq
      | n + 2, _ =>
      rw [Fin.mul_comm]
      apply Fin.val_inj.mp
      apply Int.ofNat_inj.mp
      show _ = ((1 % (n + 2)): Int)
      simp [Fin.val_mul]
      rw [Int.max_eq_left, Int.mul_emod, Int.emod_emod, ←Int.mul_emod]
      symm
      apply eq_one
      apply Nat.succ_lt_succ
      apply Nat.zero_lt_succ
      apply Int.emod_nonneg
      omega
  }

variable (n: ℕ) [Fact (Nat.IsPrime n)]

private def n_prime : Nat.IsPrime n := Fact.proof

private def toUnit_of_prime {n: ℕ} [Fact (Nat.IsPrime n)] (a: Fin n) (h: a ≠ 0) : Units (Fin n) := (Fin.toUnit a <| by
  rw [Nat.gcd_comm]
  apply (Nat.gcd_eq_one_or_dvd_of_prime (n_prime (n := n)) a.val).resolve_right
  intro g
  have := Nat.dvd_le _ _ g (by
    apply Nat.zero_lt_of_ne_zero
    intro g; apply h
    exact Eq.symm (Fin.eq_of_val_eq (Eq.symm g)))
  have := Nat.not_le_of_lt a.isLt
  contradiction)

instance : CheckedInv? (Fin n) where
  checked_invert a h := (toUnit_of_prime a h).inv

instance : CheckedDiv? (Fin n) where
  checked_div a b h := a * b⁻¹?

instance : CheckedIntPow? (Fin n) := instCheckedIntPow

instance : IsGroupWithZero (Fin n) where
  exists_ne := by
    refine ⟨0, 1, ?_⟩
    intro h
    replace h := Fin.mk.inj h
    simp at h
    have := n_prime (n := n)
    subst h
    contradiction
  mul_inv?_cancel a h := by
    show (toUnit_of_prime a h).val * (toUnit_of_prime a h).inv = _
    apply Units.val_mul_inv
  div?_eq_mul_inv? _ _ _ := rfl
  zpow?_ofNat _ _ := rfl
  zpow?_negSucc _ _ _ := rfl
