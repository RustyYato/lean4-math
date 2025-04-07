import Math.Algebra.Field.SetLike.Lattice
import Math.Data.Rat.Basic
import Math.Algebra.Impls.Fin

-- TODO: prove that for `HasChar α 0`, `⊥: α ≃+* ℚ`
-- and for `HasChar α (n + 1)`, `⊥: α ≃+* Fin (n + 1)`

private def field_char' (F: Type*) [FieldOps F] [IsField F] [HasChar F n] (h: n ≠ 0) : Nat.IsPrime n := by
  apply And.intro
  · rintro rfl
    have := HasChar.Subsingleton F
    have ⟨a, b, h⟩ := inferInstanceAs (IsNontrivial F)
    apply h; apply Subsingleton.allEq
  rintro n ⟨m, rfl⟩
  have : n • 1 * m • 1 = (0: F) := by
    rw [←natCast_eq_nsmul_one, ←natCast_eq_nsmul_one,
      ←natCast_mul, HasChar.natCast_eq_zero]
  rcases of_mul_eq_zero this with h | h
  · rw [←natCast_eq_nsmul_one] at h
    replace ⟨k, g⟩ := HasChar.char_dvd_natCast_eq_zero _ h
    match k with
    | 0 =>
      simp at g
      cases g
      right; simp
    | 1 => simp at g; right; assumption
    | k + 2 =>
    match m with
    | 0 =>
      simp at g
      cases g
      right; simp
    | m + 1 =>
      rw [mul_add, Nat.mul_succ, add_mul, add_mul] at g
      have : n * 2 ≤ n := by
        rw (occs := [2]) [g]
        omega
      match n with
      | 0 => right; simp
      | 1 => left; rfl
      | n + 2 => omega
  · rw [←natCast_eq_nsmul_one] at h
    replace ⟨k, g⟩ := HasChar.char_dvd_natCast_eq_zero _ h
    match k with
    | 0 =>
      simp at g; cases g
      simp at *
    | 1 =>
      simp at g
      rw [←g]
      match n with
      | 0 => simp at h
      | 1 => left; rfl
      | n + 2 =>
        rw [add_mul] at g
        have : 2 * m ≤ m := by omega
        match m with
        | 0 => simp at h
    | k + 2 =>
      match n with
      | 0 => simp at h
      | 1 => left; rfl
      | n + 2 =>
        rw [add_mul, add_mul, mul_add (2 * m)] at g
        have : 2 * m ≤ m := by omega
        match m with
        | 0 => simp at h

def field_char (F: Type*) [FieldOps F] [IsField F] [HasChar F n] : n = 0 ∨ Nat.IsPrime n := by
  apply Decidable.or_iff_not_imp_left.mpr
  apply field_char' F
