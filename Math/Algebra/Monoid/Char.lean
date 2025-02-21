import Math.Algebra.Monoid.Defs

open Classical

variable (α: Type*) [AddMonoidOps α] [IsAddMonoid α]

class HasChar (n: outParam <| Nat): Prop where
  spec : ∀(m: Nat), (∀(a: α), m • a = 0) ↔ n ∣ m

def HasChar.char_dvd [h: HasChar α n] : ∀(m: Nat), (∀(a: α), m • a = 0) -> n ∣ m := by
  intro m
  apply (h.spec _).mp

def HasChar.char_spec [h: HasChar α n] : ∀a: α, n • a = 0 := by
  intro m
  apply (h.spec _).mpr
  apply Nat.dvd_refl

def HasChar.eq (h: HasChar α n) (g: HasChar α m) : n = m := by
  apply Nat.dvd_antisymm
  apply h.char_dvd
  apply g.char_spec
  apply g.char_dvd
  apply h.char_spec

def HasChar.of_spec (n: ℕ) (h: ∀a: α, n • a = 0) (g: ∀(m: Nat), (∀(a: α), m • a = 0) -> n ∣ m) : HasChar α n where
  spec := by
    intro m
    apply Iff.intro
    intro s
    apply g
    assumption
    rintro ⟨k, rfl⟩
    intro a
    rw [mul_nsmul]
    apply h

def HasChar.exists : ∃n, HasChar α n := by
  by_cases h:∃n: Nat, n ≠ 0 ∧ ∀a: α, n • a = 0
  · replace h := Relation.exists_min (· < ·) h
    obtain ⟨n, ⟨npos, h⟩, min_spec⟩ := h
    exists n
    apply HasChar.mk
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
    apply HasChar.mk
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
noncomputable def char : ℕ := Classical.choose (HasChar.exists α)

def HasChar.char : HasChar α (char α) := Classical.choose_spec (HasChar.exists α)

def char_dvd : ∀(m: Nat), (∀(a: α), m • a = 0) -> char α ∣ m := (HasChar.char α).char_dvd
def char_spec : ∀(a: α), char α • a = 0 := (HasChar.char α).char_spec

def char_eq_of (n: Nat) : (∀a: α, n • a = 0) -> (∀(m: Nat), (∀(a: α), m • a = 0) -> n ∣ m) -> char α = n := by
  intro h g
  apply HasChar.eq (α := α)
  apply HasChar.char
  apply HasChar.of_spec <;> assumption

-- any additive monoid with characteristic 1 must be subsingleton
-- in fact, since it also contains `0`, it have exactly one value
instance [HasChar α 1] : Subsingleton α where
  allEq := by
    suffices ∀x: α, x = 0 by
      intro a b ; rw [this a, this b]
    intro x
    rw [←one_nsmul x, HasChar.char_spec]
