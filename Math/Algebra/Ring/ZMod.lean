import Math.Algebra.Impls.Int
import Math.Algebra.Impls.Fin
import Math.Algebra.Ring.Theory.Ideal.TwoSided.Quotient
import Math.Data.Quotient.Basic

-- the multiplies of n, as an ideal over the integers
def Int.multiples (n: ℕ) : Ideal ℤ where
  carrier := Set.mk fun x => (n: ℤ) ∣ x
  mem_zero' := by exists 0
  mem_neg' := by
    intro x hx
    apply Int.dvd_neg.mpr
    assumption
  mem_add' := by
    intro x y hx hy
    apply Int.dvd_add <;> assumption
  mem_mul_left' := by
    intro r x hx
    apply Int.dvd_trans
    assumption
    apply Int.dvd_mul_left
  mem_mul_right' := by
    intro r x hx
    apply Int.dvd_trans
    assumption
    apply Int.dvd_mul_right

def ZMod (n: ℕ): Type := (Int.multiples n).toRing

instance : RingOps (ZMod n) := inferInstanceAs (RingOps (Int.multiples n).toRing)
instance : IsRing (ZMod n) := inferInstanceAs (IsRing (Int.multiples n).toRing)

def zmod_zero_eqv_int : ZMod 0 ≃+* ℤ :=
  flip RingEquiv.trans (Ideal.eqv_quot_empty (R := ℤ)).symm <| Ideal.toRing_eqv_toRing_of_eq <| by
    ext x
    apply Iff.intro
    intro h
    cases Int.zero_dvd.mp h
    rfl
    rintro rfl
    apply Int.dvd_refl

def zmod_succ_eqv_fin (n: Nat) [h: NeZero n] : ZMod n ≃+* Fin n where
  invFun x := Ideal.mkQuot _ x.val
  toFun := by
    have n_ne_zero : n ≠ 0 := Ne.symm (NeZero.ne' n)
    apply Quotient.lift (fun x: ℤ => Fin.mk (x % n).toNat (by
      refine (Int.toNat_lt ?_).mpr ?_
      refine Int.emod_nonneg x ?_
      omega
      refine Int.emod_lt_of_pos x ?_
      omega))
    intro a b eqv
    replace eqv: (n: ℤ) ∣ a - b := eqv
    congr 1
    apply Int.ofNat_inj.mp
    rw [Int.toNat_of_nonneg, Int.toNat_of_nonneg]
    · rw [←Int.ediv_add_emod a n, ←Int.ediv_add_emod b n,
        sub_add] at eqv
      rw [sub_eq_add_neg, add_comm, add_sub_assoc, ←add_assoc, add_comm (-_),
        ←sub_eq_add_neg, ←mul_sub] at eqv
      replace eqv := (Int.dvd_iff_dvd_of_dvd_add eqv).mp (Int.dvd_mul_right _ _)
      obtain ⟨x, hx⟩ := eqv
      apply eq_of_sub_eq_zero
      rw [hx]
      refine Int.mul_eq_zero.mpr ?_; right
      have : (a % n - b % n).natAbs < n := by
        apply Int.ofNat_lt.mp
        rcases le_total (a % n) (b % n) with h | h
        rw [←Int.natAbs_neg, neg_sub, Int.natAbs_of_nonneg]
        refine Int.sub_lt_iff.mpr ?_
        apply lt_of_lt_of_le
        apply Int.emod_lt_of_pos
        omega
        apply Int.le_add_of_nonneg_right
        refine Int.emod_nonneg a ?_
        omega
        omega
        rw [Int.natAbs_of_nonneg]
        refine Int.sub_lt_iff.mpr ?_
        apply lt_of_lt_of_le
        apply Int.emod_lt_of_pos
        omega
        apply Int.le_add_of_nonneg_right
        refine Int.emod_nonneg b ?_
        omega
        omega
      match x with
      | 0 => rfl
      | .ofNat (x + 1) =>
        replace hx : _ = _ * ((x + 1: ℕ): ℤ) := hx
        rw [Int.ofNat_succ, mul_add, mul_one] at hx
        rw [hx, ←Int.ofNat_mul, ←Int.ofNat_add, Int.natAbs_ofNat] at this
        omega
      | .negSucc x =>
        rw [hx, Int.natAbs_mul, Int.natAbs_negSucc, Int.natAbs_ofNat,
          Nat.mul_succ] at this
        omega
    refine Int.emod_nonneg _ ?_
    omega
    refine Int.emod_nonneg _ ?_
    omega
  rightInv := by
    intro x
    apply Fin.val_inj.mp
    show x.val % n = x
    rw [Nat.mod_eq_of_lt]
    apply Fin.isLt
  leftInv := by
    intro x
    induction x using Quot.ind with | mk x =>
    apply Quotient.sound
    dsimp
    show (n: ℤ) ∣ _ - _
    rw [Int.toNat_of_nonneg]
    conv => { rhs; rhs; rw [←Int.ediv_add_emod x n] }
    rw [sub_eq_add_neg, neg_add_rev, ←add_assoc, add_neg_cancel, zero_add]
    apply Int.dvd_neg.mpr
    apply Int.dvd_mul_right
    refine Int.emod_nonneg _ ?_
    refine Int.ofNat_ne_zero.mpr ?_
    exact Ne.symm (NeZero.ne' n)
  resp_zero := rfl
  resp_one := rfl
  resp_add := by
    intro a b
    dsimp
    cases a using Quotient.ind
    cases b using Quotient.ind
    rename_i a b
    show Quotient.lift _ _ (Quotient.mk _ (a + b)) = _
    rw [Quotient.mk_lift, Quotient.mk_lift, Quotient.mk_lift]
    congr
    have n_ne_zero : n ≠ 0 := Ne.symm (NeZero.ne' n)
    apply Int.ofNat_inj.mp
    erw [←Int.ofNat_mod_ofNat, Int.ofNat_add, Int.toNat_of_nonneg,
      Int.toNat_of_nonneg, Int.toNat_of_nonneg, Int.add_emod]
    all_goals
    refine Int.emod_nonneg _ ?_
    omega
  resp_mul := by
    intro a b
    dsimp
    cases a using Quotient.ind
    cases b using Quotient.ind
    rename_i a b
    show Quotient.lift _ _ (Quotient.mk _ (a * b)) = _
    rw [Quotient.mk_lift, Quotient.mk_lift, Quotient.mk_lift]
    congr
    have n_ne_zero : n ≠ 0 := Ne.symm (NeZero.ne' n)
    apply Int.ofNat_inj.mp
    erw [←Int.ofNat_mod_ofNat, Int.ofNat_mul, Int.toNat_of_nonneg,
      Int.toNat_of_nonneg, Int.toNat_of_nonneg, Int.mul_emod]
    all_goals
    refine Int.emod_nonneg _ ?_
    omega
