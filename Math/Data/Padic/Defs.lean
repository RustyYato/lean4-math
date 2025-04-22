import Math.Data.Rat.Order
import Math.Algebra.QAlgebra.Basic
import Math.Data.CauchySeq.Completion.Basic
import Math.Data.Nat.Find

-- a type synonym for Rat which has a different norm
def PadicRat (_: ℕ) := ℚ

namespace PadicRat

instance : FieldOps (PadicRat p) := inferInstanceAs (FieldOps ℚ)
instance : IsField (PadicRat p) := inferInstanceAs (IsField ℚ)
instance : IsCommMagma (PadicRat p) := inferInstanceAs (IsCommMagma ℚ)
instance : HasChar (PadicRat p) 0 := inferInstanceAs (HasChar ℚ 0)
instance : Nonempty (PadicRat p) := inferInstanceAs (Nonempty ℚ)
instance : RatCast (PadicRat p) := inferInstanceAs (RatCast ℚ)
instance : SMul ℚ (PadicRat p) := inferInstanceAs (SMul ℚ ℚ)
instance : IsQAlgebra (PadicRat p) := inferInstanceAs (IsQAlgebra ℚ)

instance : LatticeOps (PadicRat p) := inferInstanceAs (LatticeOps ℚ)
instance : IsDecidableLinearOrder (PadicRat p) := inferInstanceAs (IsDecidableLinearOrder ℚ)

def equivRat : (PadicRat p) ≃+* ℚ := RingEquiv.refl

def valuation_pred (p x: ℕ) :
  ∃ n, (fun n => (p ^ (x - n) ∣ x)) n := ⟨x, by simp⟩

def valuation' (p x: ℕ) : ℕ :=
  x - Nat.findP (valuation_pred p x)

def valuation (p x: ℕ) : Option ℕ :=
  if p = 1 || x = 0 then
    .none
  else
    valuation' p x

def valuation'_dvd (p x: ℕ) : p ^ (valuation' p x) ∣ x := by
  have := Nat.findP_spec (valuation_pred p x)
  simp at this
  assumption

def valuation'_spec (p x: ℕ) (hp: p ≠ 1) (hx: x ≠ 0) : ∀n: ℕ, n ≤ valuation' p x ↔ p ^ n ∣ x := by
  intro n
  apply Iff.intro
  · intro h
    apply flip Nat.dvd_trans
    apply valuation'_dvd p x
    apply Nat.pow_dvd_pow
    assumption
  · intro h
    show _ ≤ x - _
    rw [Nat.le_sub_iff_add_le, Nat.add_comm, ←Nat.le_sub_iff_add_le]
    rw [←Nat.not_lt]
    intro g
    replace g : x - _ < _ := g
    have := Nat.lt_findP_spec (valuation_pred p x) _ g
    simp at this
    rw [Nat.sub_sub_self] at this
    contradiction
    clear g this
    iterate 2
      match p with
      | 0 =>
        match n with
        | 0 => apply Nat.zero_le
        | n + 1 =>
          simp at h
          subst h
          contradiction
      | p + 2 =>
        clear hp
        induction n with
        | zero => apply Nat.zero_le
        | succ n ih =>
          have := ih (Nat.dvd_trans (by apply Nat.dvd_mul_right) h)
          rcases Nat.lt_or_eq_of_le this
          apply Nat.succ_le_of_lt
          assumption
          subst x
          clear this ih
          exfalso
          match n with
          | n + 1 =>
          clear hx
          obtain ⟨k, hk⟩ := h
          rw [Nat.add_assoc] at hk; simp at hk
          have : 0 < k := by
            apply Nat.zero_lt_of_ne_zero
            rintro rfl
            contradiction
          have : 2  ^ (n + 2) ≤ (p + 2) ^ (n + 2) * k := by
            rw [←Nat.mul_one (2 ^ _)]
            apply Nat.mul_le_mul
            apply Nat.pow_le_pow_left
            omega
            omega
          rw [←hk, ←Nat.not_lt] at this
          apply this; clear this hk; clear this
          clear k p; clear p
          rename_i m; clear m
          induction n with
          | zero => decide
          | succ n ih =>
            apply Nat.lt_of_lt_of_le
            apply Nat.add_lt_add_of_lt_of_le
            assumption
            rfl
            rw (occs := [2]) [Nat.pow_succ]
            rw [Nat.mul_two]
            apply Nat.add_le_add
            rfl
            omega
    · rw [←Nat.not_lt]
      intro g
      have := Nat.lt_findP_spec (valuation_pred p x) x g
      simp at this

-- valuation is none exactly when there is no max `n`, such that `p ^ n ∣ x`
def valuation_eq_none_iff (p x: ℕ) : valuation p x = .none ↔ ∀n, p ^ n ∣ x -> ∃m, p ^ m ∣ x ∧ n < m := by
  apply Iff.intro
  · intro h
    unfold valuation at h
    simp only [Bool.or_eq_true, decide_eq_true_eq, ite_eq_left_iff, not_or, reduceCtorEq, imp_false,
      Decidable.not_not, Decidable.not_and_iff_not_or_not] at h
    rcases h with rfl | rfl
    intro n
    intro h
    exists n + 1
    simp
    intro n h
    exists n + 1
    simp
  · intro h
    unfold valuation
    simp
    intro g
    apply Decidable.byContradiction
    intro h'; apply g; clear g
    match x with
    | x + 1 =>
    clear h'
    match p with
    | 1 => rfl
    | 0 =>
      have := h 0
      simp at this
      obtain ⟨m, hm, _⟩ := this
      match m with
      | m + 1 =>
      simp at hm
    | p + 2 =>
      exfalso
      have ⟨m, hm, val_lt⟩ := h (valuation' (p + 2) (x + 1)) (valuation'_dvd (p + 2) (x + 1))
      have := (valuation'_spec (p + 2) (x + 1) ?_ ?_ m).mpr hm
      rw [←Nat.not_le] at val_lt
      contradiction
      omega
      omega

def znorm (p: ℕ) (x: ℤ) : ℚ :=
  if hp:p < 2 then
    -- if `p = 0 ∨ p = 1`, then use the trivial norm
    if x = 0 then 0 else 1
  else
    have : p ≠ 0 := by omega
    match valuation p x.natAbs with
    | .some n => ((1: ℚ) /? (p: ℚ)) ^ n
    | .none => 0

def znorm_ne_zero_of_ne_zero (p: ℕ) (x: ℤ) (hx: x ≠ 0) : znorm p x ≠ 0 := by
  intro h
  unfold znorm  at h
  simp at h
  split at h
  contradiction
  split at h
  revert h
  invert_tactic
  clear h; rename_i h
  unfold valuation at h
  simp at h
  apply hx; apply h
  rintro rfl
  contradiction

@[simp]
def valuation_zero : valuation p 0 = .none := by
  unfold valuation
  simp

def valuation_eq_some_iff (p x: ℕ) : valuation p x = .some (valuation' p x) ↔ p ≠ 1 ∧ x ≠ 0 := by
  unfold valuation
  simp

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply znorm_ne_zero_of_ne_zero <;> invert_tactic)

def norm' (p: ℕ) (x: Rat.Fract) : ℚ :=
  znorm p x.num /? znorm p x.den ~(by
    apply znorm_ne_zero_of_ne_zero
    intro h
    rw [←natCast_zero] at h
    exact x.den_nz (HasChar.natCast_inj h))

def valuation'_mul (p a b: ℕ) [Nat.IsPrimeClass p] (ha: a ≠ 0) (hb: b ≠ 0) :
  valuation' p (a * b) = valuation' p a + valuation' p b := by
  apply flip le_antisymm
  · apply (valuation'_spec _ _ _ _ _).mpr
    rw [npow_add]
    apply Nat.mul_dvd_mul
    apply valuation'_dvd
    apply valuation'_dvd
    rintro rfl
    contradiction
    intro hab
    cases of_mul_eq_zero hab <;> contradiction
  · rw [←Nat.not_lt]
    intro g
    have := (valuation'_spec _ _ (by
      rintro rfl
      contradiction) ?_ _).mp (Nat.succ_le_of_lt g)
    rw [←Nat.add_succ, npow_add] at this
    have pprime := Nat.prime p
    have ⟨ka, ka_eq⟩ := valuation'_dvd p a
    have ⟨kb, kb_eq⟩ := valuation'_dvd p b
    rw [npow_succ] at this
    conv at this => {
      rhs; rw [ka_eq, kb_eq]
    }
    rw [mul_assoc] at this
    replace := Nat.dvd_of_mul_dvd_mul_left ?_ this
    rw [mul_left_comm] at this
    replace := Nat.dvd_of_mul_dvd_mul_left ?_ this
    replace := Nat.prime_dvd_mul (Nat.prime p) ka kb this
    cases this
    · have : p ^ (valuation' p a).succ ∣ a := by
        conv => { rhs; rw [ka_eq] }
        rw [npow_succ]
        apply Nat.mul_dvd_mul_left
        assumption
      rw [←valuation'_spec] at this
      omega
      rintro rfl
      contradiction
      assumption
    · have : p ^ (valuation' p b).succ ∣ b := by
        conv => { rhs; rw [kb_eq] }
        rw [npow_succ]
        apply Nat.mul_dvd_mul_left
        assumption
      rw [←valuation'_spec] at this
      omega
      rintro rfl
      contradiction
      assumption
    · apply Nat.pow_pos
      refine Nat.zero_lt_of_ne_zero ?_
      rintro rfl
      contradiction
    · apply Nat.pow_pos
      refine Nat.zero_lt_of_ne_zero ?_
      rintro rfl
      contradiction
    · intro h
      cases of_mul_eq_zero h <;> contradiction

def znorm_mul (p: ℕ) [Nat.IsPrimeClass p] (x y: ℤ) : znorm p x * znorm p y = znorm p (x * y) := by
  unfold znorm
  simp
  have : ¬(p < 2) := by
    rename_i h
    intro; match p, h with | 0, h | 1, h => contradiction
  repeat rw [dif_neg this]
  unfold valuation
  simp
  by_cases h:x * y = 0
  rcases of_mul_eq_zero h with rfl | rfl
  simp
  simp
  rw [if_neg, if_neg, if_neg]
  simp
  rw [←npow_add, ←valuation'_mul, Int.natAbs_mul]
  intro g; rw [Int.natAbs_eq_zero] at g; subst x; simp at h
  intro g; rw [Int.natAbs_eq_zero] at g; subst y; simp at h
  intro g; rcases g with rfl | g <;> contradiction
  intro g; rcases g with rfl | g; contradiction; subst y; simp at h
  intro g; rcases g with rfl | g; contradiction; subst x; simp at h

def norm'_spec (p: ℕ) [Nat.IsPrimeClass p] (a b: Rat.Fract) (h: a ≈ b) : norm' p a = norm' p b := by
  unfold norm'
  unfold znorm
  replace h : _ = _ := h
  have a_ne_zero_iff_b_ne_zero : a.num = 0 ↔ b.num = 0 := by
    apply Iff.intro
    intro ha; rw [ha] at h
    simp at h
    apply (of_mul_eq_zero h.symm).resolve_right
    apply a.den_nz'
    intro hb; rw [hb] at h
    simp at h
    apply (of_mul_eq_zero h).resolve_right
    apply b.den_nz'
  split
  conv => { lhs; arg 2; rw [if_neg (by exact a.den_nz')] }
  conv => { rhs; arg 2; rw [if_neg (by exact b.den_nz')] }
  simp
  split
  rw [if_pos]
  rwa [←a_ne_zero_iff_b_ne_zero]
  rw [if_neg]
  rwa [←a_ne_zero_iff_b_ne_zero]
  by_cases ha:a.num = 0
  have hb : b.num = 0 := by rwa [←a_ne_zero_iff_b_ne_zero]
  simp [ha, hb]
  have hb : b.num ≠ 0 := by rwa [a_ne_zero_iff_b_ne_zero] at ha
  simp
  rw [(valuation_eq_some_iff _ _).mpr, (valuation_eq_some_iff _ b.num.natAbs).mpr]
  conv => {
    lhs; arg 2; rw [(valuation_eq_some_iff _ _).mpr (by
      apply And.intro
      rintro rfl; contradiction
      apply a.den_nz)]
  }
  conv => {
    rhs; arg 2; rw [(valuation_eq_some_iff _ _).mpr (by
      apply And.intro
      rintro rfl; contradiction
      apply b.den_nz)]
  }
  simp
  rw [div?_eq_mul_inv?]; conv => { rhs; rw [div?_eq_mul_inv?] }
  rw [inv?_npow', inv?_npow', ←zpow?_ofNat, ←zpow?_ofNat,
    ←zpow?_add, ←zpow?_add]
  congr 1
  · apply add_right_cancel
    rw [add_assoc, neg_add_cancel, add_zero]
    rw [add_comm_right]
    apply add_right_cancel
    rw [add_assoc, neg_add_cancel, add_zero]
    rw [←natCast_add, ←natCast_add]
    congr 1
    rw [←valuation'_mul, ←valuation'_mul]
    congr 1
    rw [←Int.natAbs_ofNat b.den, ←Int.natAbs_ofNat a.den,
      ←Int.natAbs_mul, ←Int.natAbs_mul, h]
    intro h
    have := Int.natAbs_eq_zero.mp h; contradiction
    apply a.den_nz
    intro h
    have := Int.natAbs_eq_zero.mp h; contradiction
    apply b.den_nz
  invert_tactic
  invert_tactic
  apply And.intro
  omega
  omega
  apply And.intro
  omega
  omega

variable [Nat.IsPrimeClass p]

def norm : PadicRat p -> ℚ :=
  Quotient.lift (norm' p) (norm'_spec p)

instance : Norm (PadicRat p) ℚ where
  norm := norm

def norm_zero_iff' {x: PadicRat p} : norm x = 0 ↔ x = 0 := by
  apply Iff.intro
  · induction x using Rat.ind with | mk x =>
    show norm' _ x = 0 -> Rat.mk x = 0
    intro h
    cases of_mul_eq_zero h
    apply Decidable.byContradiction
    intro g
    rename_i h
    apply Decidable.not_not.mpr h
    apply znorm_ne_zero_of_ne_zero
    intro h; apply g; clear g
    apply Rat.sound
    apply (Rat.Fract.eq_zero_iff_num_eq_zero _).mpr
    assumption
    exfalso; rename_i h
    apply Decidable.not_not.mpr h
    invert_tactic
  · rintro rfl
    show norm' _ 0 = 0
    unfold norm'
    simp
    show znorm p 0 /? znorm p 1 = 0
    unfold znorm
    simp

def norm_one' : norm (1: PadicRat p) = 1 := div?_self _ _

def norm_neg' (a: PadicRat p) : norm (-a) = norm a := by
  induction a using Rat.ind with | mk a =>
  show norm' _ (-a) = norm' _ a
  unfold norm'
  congr 1
  unfold znorm
  simp

def norm_mul' (a b: PadicRat p) : norm (a * b) = norm a * norm b := by
  induction a using Rat.ind with | mk a =>
  induction b using Rat.ind with | mk b =>
  rw [Rat.mk_mul]
  show norm' _ _ = norm' _ _ * (norm' _ _)
  unfold norm'
  rw [mul_div?_mul]
  congr
  rw [znorm_mul]; rfl
  rw [znorm_mul]; rfl

def norm_add_le_add_norm (a b: PadicRat p) : norm (a + b) ≤ norm a + norm b := by
  sorry

instance [Nat.IsPrimeClass p] : IsAlgebraNorm (PadicRat p) where
  norm_zero_iff := norm_zero_iff'
  norm_one := norm_one'
  norm_mul := norm_mul'
  norm_neg := norm_neg'
  norm_add_le_add_norm := norm_add_le_add_norm

end PadicRat
