import Math.Algebra.Monoid.Defs

open Classical
variable (α: Type*) [AddMonoidOps α] [IsAddMonoid α]

private
def HasChar (n: Nat) : Prop := ∀(m: Nat), (∀(a: α), m • a = 0) ↔ n ∣ m

private
def existsChar : ∃n, HasChar α n := by
  by_cases h:∃n: Nat, n ≠ 0 ∧ ∀a: α, n • a = 0
  · replace h := Relation.exists_min (· < ·) h
    obtain ⟨n, ⟨npos, h⟩, min_spec⟩ := h
    exists n
    intro m
    apply Iff.intro
    · intro g
      induction m using Nat.strongRecOn with
      | ind m ih =>
      cases m with
      | zero => apply Nat.dvd_zero
      | succ m =>
      have : n ≤ m + 1 := by
        apply Nat.le_of_not_lt
        intro lt
        refine min_spec (m+1) lt ⟨?_, ?_⟩
        intro; contradiction
        assumption
      have := Nat.div_add_mod (m+1) n
      rw [←this] at g; clear this
      conv at g => { intro a; rw [add_nsmul, mul_nsmul, h, zero_add] }
      have := ih ((m+1) % n) ?_ g
      rw [←Nat.div_add_mod (m + 1) n]
      apply Nat.dvd_add
      apply Nat.dvd_mul_right
      assumption
      apply Nat.lt_of_lt_of_le
      apply Nat.mod_lt
      apply Nat.pos_of_ne_zero
      assumption
      assumption
    · intro ⟨k, dvd⟩ a
      rw [dvd, mul_nsmul, h]
  · exists 0
    intro m
    apply Iff.intro
    · intro g
      cases m
      apply Nat.dvd_refl
      rename_i m
      have := h ⟨m+1, Ne.symm (Nat.zero_ne_add_one m), g⟩
      contradiction
    · intro g
      cases Nat.eq_zero_of_zero_dvd g
      intro
      rw [zero_nsmul]

-- the characteristic of a Addition Monoid over α
-- i.e. the smallest non-zero natural such that
-- the product with any element of α is zero
-- or if no such non-zero natural exists, then zero
noncomputable def char : ℕ := Classical.choose (existsChar α)

def char_dvd : ∀(m: Nat), (∀(a: α), m • a = 0) -> char α ∣ m := fun m => (Classical.choose_spec (existsChar α) m).mp
def char_spec : ∀(a: α), char α • a = 0 := (Classical.choose_spec (existsChar α) _).mpr (Nat.dvd_refl _)
def char_eq_of (n: Nat) : (∀a: α, n • a = 0) -> (∀(m: Nat), (∀(a: α), m • a = 0) -> n ∣ m) -> char α = n := by
  intro h g
  apply Nat.dvd_antisymm
  apply char_dvd
  assumption
  apply g
  apply char_spec
