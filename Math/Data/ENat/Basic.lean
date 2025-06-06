import Math.Data.ENat.Defs
import Math.Algebra.Semiring.Order.Defs
import Math.Algebra.Semiring.Char
import Math.Algebra.Algebra.Defs

namespace ENat

instance : SMul ℕ ℕ∞ where
  smul n m := n * m

instance : Pow ℕ∞ ℕ where
  pow n m := n ^ (m: ℕ∞)

@[simp]
private def one_mul (a: ℕ∞) : 1 * a = a := by
  cases a
  erw [natCast_mul_natCast]
  simp; rfl

@[simp]
private def mul_one (a: ℕ∞) : a * 1 = a := by
  cases a
  erw [natCast_mul_natCast]
  simp; rfl

@[simp]
private def zero_add (a: ℕ∞) : 0 + a = a := by
  cases a
  erw [natCast_add_natCast]
  simp; rfl

@[simp]
private def add_zero (a: ℕ∞) : a + 0 = a := by
  cases a
  erw [natCast_add_natCast]
  simp; rfl

instance : IsCommMagma ℕ∞ where
  mul_comm a b := by
    cases a <;> cases b <;> simp
    rw [mul_comm]
    iterate 2
      rename_i n
      cases n
      rfl
      rfl

instance : IsSemiring ℕ∞ where
  add_assoc a b c := by
    cases a <;> cases b <;> cases c <;> simp
    rw [add_assoc]
  add_comm a b := by
    cases a <;> cases b <;> simp
    rw [add_comm]
  zero_add := by simp
  add_zero := by simp
  natCast_succ _ := rfl
  natCast_zero := rfl
  mul_assoc a b c := by
    cases a <;> cases b <;> cases c <;> simp
    rw [mul_assoc]
    all_goals
      rename_i n
      cases n
      simp
    any_goals
      rename_i n _
      cases n
      simp
    all_goals rfl
  zero_mul a := by simp
  mul_zero a := by simp
  one_mul := by simp
  mul_one := by simp
  mul_add a b c := by
    cases a <;> cases b <;> cases c <;> simp
    rw [mul_add]
    iterate 2
      rename_i n _
      cases n
      simp; rfl
    rename_i n
    cases n
    rfl
    rfl
    rename_i n m
    cases n <;> cases m <;> rfl
  add_mul a b c := by
    cases a <;> cases b <;> cases c <;> simp
    rw [add_mul]
    rename_i n m
    cases n <;> cases m <;> rfl
    iterate 3
      rename_i n
      cases n
      rfl
      rfl
  zero_nsmul a := by
    show 0 * a = 0
    simp
  succ_nsmul := by
    intro n a
    show (n + 1: ℕ) * a = n * a + a
    cases a
    rename_i a
    cases a
    simp
    erw [natCast_mul_natCast, natCast_mul_natCast,
      natCast_add_natCast]
    rw [add_mul]
    simp
    simp
    rfl
  npow_zero := pow_zero
  npow_succ n a := by
    show pow _ _ = pow _ _ * _
    unfold pow
    split
    any_goals trivial
    rename_i h; nomatch h
    · split
      any_goals trivial
      erw [mul_one]
      rename_i h g
      cases h; cases g
      simp
    · split
      any_goals rfl
      erw [mul_zero]
    · split
      any_goals trivial
    · split
      any_goals trivial
      simp
      rename_i h _ _ g
      cases h; cases g
      simp
      iterate 2
        rename_i h _ _ g _
        cases h; cases g
        simp; try rfl
      rename_i h g
      cases h; cases g
      rename_i h _ _ _ _ _
      cases h
      erw [npow_succ, natCast_mul_natCast]

instance : IsOrderedCommMonoid ℕ∞ where
  mul_le_mul_left a b h c := by
    cases h
    refine if hc:c = 0 then ?_ else ?_
    simp [hc]
    cases c
    simp [hc]
    rename_i c
    erw [mul_inf]
    apply le_top
    assumption
    apply le_top
    cases c
    simp
    apply mul_le_mul_left
    assumption
    rename_i c h
    cases c
    simp
    cases Nat.le_zero.mp h
    simp
    rw (occs := [2]) [inf_mul]
    simp
    nofun

instance : IsStrictOrderedSemiring ℕ∞ where
  zero_le_one := by apply bot_le
  add_le_add_left := by
    intro a b h c
    cases h
    simp
    cases c
    apply (natCast_le_natCast _ _).mpr
    apply add_le_add_left
    assumption
    rfl
  mul_nonneg _ _ _ _ := by apply bot_le
  mul_le_mul_of_nonneg_left _ _ _ _ _ := by
    apply mul_le_mul_left
    assumption
  mul_le_mul_of_nonneg_right _ _ _ _ _ := by
    apply mul_le_mul_right
    assumption
  mul_pos := by
    intro a b h g
    cases h
    cases g
    · apply natCast_lt_inf
    · rename_i n _
      match n with
      | n + 1 =>
      apply natCast_lt_inf
    · cases b
      erw [natCast_mul_natCast]
      apply (natCast_lt_natCast _ _).mpr
      apply mul_pos
      assumption
      rw [←natCast_lt_natCast]
      assumption
      rename_i n _
      match n with
      | n + 1 =>
      apply natCast_lt_inf

instance : HasChar ℕ∞ 0 := HasChar.of_ring_emb {
  algebraMap (R := ℕ) (α := ℕ∞) with
  inj' _ _ := ENat.ofNat.inj
}

end ENat
