import Math.Data.Cardinal.Algebra
import Math.Data.ENat.Basic

namespace ENat

private def toCard' : ℕ∞ -> Cardinal
| ∞ => ℵ₀
| (n: ℕ) => n

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
    · erw [natCast_add_natCast]
      unfold ENat.toCard'
      simp
      rw [natCast_add]
    · unfold ENat.toCard'
      simp
      rw [add_comm, Cardinal.aleph0_add_fin]
    · unfold ENat.toCard'
      simp
      rw [Cardinal.aleph0_add_fin]
    · unfold ENat.toCard'
      simp
      rw [Cardinal.aleph0_add_aleph0]
  map_mul := by
    intro x y
    cases x <;> cases y
    · erw [natCast_mul_natCast]
      unfold ENat.toCard'
      simp
      rw [natCast_mul]
    · rename_i n
      cases n
      simp
      simp only [←ENat.natCast_zero]
      unfold ENat.toCard'
      simp [natCast_zero]
      rename_i n
      erw [ENat.mul_inf (n + 1: ℕ) nofun]
      unfold ENat.toCard'
      simp
      rw [mul_comm, Cardinal.aleph0_mul_fin]
    · rename_i n
      cases n
      simp
      unfold ENat.toCard'
      simp [natCast_zero]
      unfold ENat.toCard'
      simp
      rename_i n
      erw [ENat.inf_mul (n + 1: ℕ) nofun]
      rw [Cardinal.aleph0_mul_fin]
    · unfold ENat.toCard'
      simp
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

end Cardinal
