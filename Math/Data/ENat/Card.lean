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

end ENat

namespace Cardinal

open ENat

private noncomputable def toENat' (c: Cardinal) : ENat :=
  open scoped Classical in
  if h:c < ℵ₀ then
    (Classical.choose ((Cardinal.lt_aleph₀ c).mp h): ℕ)
  else
    ∞

private def toENat'_natCast (n: ℕ) : toENat' n = n := by
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

-- noncomputable def toENat : Cardinal →+* ENat where
--   toFun := toENat'
--   map_zero := by
--     rw [←natCast_zero, toENat'_natCast]; rfl
--   map_one := by
--     rw [←natCast_one, toENat'_natCast]; rfl
--   map_add {x y} := by
--     cases x using cases with
--     | natCast x =>
--       cases y using cases with
--       | natCast y =>
--         sorry
--       | inf => sorry
--     | inf => sorry
--   map_mul := sorry

end Cardinal
