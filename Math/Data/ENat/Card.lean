import Math.Data.Cardinal.Algebra
import Math.Data.ENat.Basic

namespace ENat

private def toCard' : ℕ∞ -> Cardinal
| ∞ => ℵ₀
| (n: ℕ) => n

@[simp] private def toCard'_ofNat (n: ℕ) : toCard' (.ofNat n) = n := rfl
@[simp] private def toCard'_natCast (n: ℕ) : toCard' n = n := rfl
@[simp] private def toCard'_inf : toCard' ∞ = ℵ₀ := rfl

def toCard : ℕ∞ ↪+* Cardinal where
  toFun := toCard'
  inj' := by
    intro x y h
    unfold toCard' at h
    cases x <;> cases y
    · simp at h
      have := Cardinal.natCast_inj h
      rw [this]
    · simp at h
      rename_i n
      have := Cardinal.natCast_lt_aleph₀ n
      rw [h] at this
      have := lt_irrefl this
      contradiction
    · simp at h
      rename_i n
      have := Cardinal.natCast_lt_aleph₀ n
      rw [h] at this
      have := lt_irrefl this
      contradiction
    · rfl
  map_zero := rfl
  map_one := rfl
  map_add := by
    intro x y
    cases x <;> cases y
    · simp [natCast_add_natCast]
      rw [natCast_add]
    · simp
      rw [add_comm, Cardinal.aleph0_add_fin]
    · simp
      rw [Cardinal.aleph0_add_fin]
    · simp
      rw [Cardinal.aleph0_add_aleph0]
  map_mul := by
    intro x y
    cases x <;> cases y
    · erw [natCast_mul_natCast]
      simp
      rw [natCast_mul]
    · rename_i n
      cases n
      simp
      simp only [←ENat.natCast_zero, ENat.toCard'_natCast]
      simp
      rename_i n
      erw [ENat.mul_inf (n + 1: ℕ) nofun]
      simp
      rw [mul_comm, Cardinal.aleph0_mul_fin]
    · rename_i n
      cases n
      simp
      simp only [←ENat.natCast_zero, ENat.toCard'_natCast]
      simp
      erw [ENat.inf_mul]
      simp
      rw [Cardinal.aleph0_mul_fin]
      nofun
    · simp
      rw [Cardinal.aleph0_mul_aleph0]

@[simp] def toCard_ofNat (n: ℕ) : toCard (.ofNat n) = n := rfl
@[simp] def toCard_natCast (n: ℕ) : toCard n = n := rfl
@[simp] def toCard_inf : toCard ∞ = ℵ₀ := rfl

end ENat

namespace Cardinal

open ENat

private noncomputable def toENat' (c: Cardinal) : ENat :=
  open scoped Classical in
  if h:c < ℵ₀ then
    (Classical.choose ((Cardinal.lt_aleph₀ c).mp h): ℕ)
  else
    ∞

@[simp] private def toENat'_natCast (n: ℕ) : toENat' n = n := by
  have : ∃x: ℕ, (n: Cardinal) = ↑x := ⟨n, rfl⟩
  unfold toENat'
  rw [dif_pos (natCast_lt_aleph₀ _)]
  show ((Classical.choose this: ℕ): ENat) = (n: ENat)
  have := Classical.choose_spec this
  rw [Cardinal.natCast_inj.eq_iff] at this
  rw [←this]

private def toENat'_inf (c: Cardinal) (hc: ℵ₀ ≤ c) : toENat' c = ∞ := by
  unfold Cardinal.toENat'
  rw [dif_neg]
  rwa [not_lt]

private def cases (motive: Cardinal -> Prop)
  (natCast: ∀n: ℕ, motive n)
  (inf: ∀c: Cardinal, ℵ₀ ≤ c -> motive c)
  (c: Cardinal) : motive c := by
  rcases lt_or_le c ℵ₀ with h | h
  rw [lt_aleph₀] at h
  obtain ⟨n, rfl⟩ := h
  apply natCast
  apply inf
  assumption

private def rightInv' (c: Cardinal) : c.toENat'.toCard = c ⊓ ℵ₀ := by
  cases c using cases
  simp
  rw [min_eq_left.mpr]
  apply le_of_lt
  apply natCast_lt_aleph₀
  rename_i h
  simp [toENat'_inf _ h]
  rw [min_eq_right.mpr]
  assumption

private def leftInv' : Function.IsLeftInverse toENat' toCard := by
  intro n
  cases n
  simp
  simp
  rw [toENat'_inf]
  rfl

noncomputable def toENat : Cardinal.{u} →+* ENat where
  toFun := toENat'
  map_zero := by
    rw [←natCast_zero, toENat'_natCast]; rfl
  map_one := by
    rw [←natCast_one, toENat'_natCast]; rfl
  map_add {x y} := by
    apply toCard.{u}.inj
    rw [map_add, rightInv', rightInv', rightInv']

    cases x using cases with
    | natCast x =>
      cases y using cases with
      | natCast y =>
        rw [←natCast_add, min_eq_left.mpr, min_eq_left.mpr, min_eq_left.mpr]
        rw [natCast_add]
        all_goals
          apply le_of_lt
          apply natCast_lt_aleph₀
      | inf =>
        rw [min_eq_right.mpr, min_eq_left.mpr, min_eq_right.mpr,
          add_comm, aleph0_add_fin]
        assumption
        apply le_of_lt
        apply natCast_lt_aleph₀
        apply le_trans
        assumption
        apply le_add_left
        apply bot_le
    | inf _ h =>
      open scoped Classical in
      rw [min_eq_right.mpr, min_eq_right.mpr h, min_def]
      split
      rw [aleph0_add_countable]
      assumption
      rw [aleph0_add_aleph0]
      apply le_trans
      assumption
      apply le_add_right
      apply bot_le
  map_mul {x y} := by
    apply toCard.{u}.inj
    rw [map_mul, rightInv', rightInv', rightInv']
    cases x using cases with
    | natCast x =>
      match x with
      | 0 => simp [min_eq_left.mpr (show 0 ≤ ℵ₀ from bot_le _)]
      | x + 1 =>
      cases y using cases with
      | natCast y =>
        rw [←natCast_mul, min_eq_left.mpr, min_eq_left.mpr, min_eq_left.mpr]
        rw [natCast_mul]
        all_goals
          apply le_of_lt
          apply natCast_lt_aleph₀
      | inf =>
        rw [min_eq_right.mpr, min_eq_left.mpr, min_eq_right.mpr,
          mul_comm, aleph0_mul_fin]
        assumption
        apply le_of_lt
        apply natCast_lt_aleph₀
        apply le_trans
        assumption
        apply le_mul_left
        apply Cardinal.natCast_le_natCast_iff.mpr
        omega
    | inf _ h =>
      by_cases hy:y = 0
      subst y
      simp [min_eq_left.mpr (show 0 ≤ ℵ₀ from bot_le _)]
      open scoped Classical in
      rw [min_eq_right.mpr, min_eq_right.mpr h, min_def]
      split
      rw [aleph0_mul_countable]
      assumption
      assumption
      rw [aleph0_mul_aleph0]
      apply le_trans
      assumption
      apply le_mul_right
      cases y using cases
      · rename_i y
        match y with
        | y + 1 =>
        apply Cardinal.natCast_le_natCast_iff.mpr
        omega
      · apply flip le_trans
        assumption
        apply le_of_lt
        apply natCast_lt_aleph₀

def toENat_toCard (c: Cardinal) : c.toENat.toCard = c ⊓ ℵ₀ := rightInv' _

def toENat_inf (c: Cardinal) (hc: ℵ₀ ≤ c) : c.toENat = ∞ := toENat'_inf c hc

def leftInv : Function.IsLeftInverse toENat toCard := leftInv'

end Cardinal

def ENat.toCard_toENat (n: ℕ∞) : n.toCard.toENat = n := Cardinal.leftInv' _
