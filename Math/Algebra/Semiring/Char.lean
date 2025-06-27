import Math.Algebra.Monoid.Char
import Math.Algebra.Semiring.Defs
import Math.Algebra.AddMonoidWithOne.Hom

def HasChar.of_natCast_eq_zero [SemiringOps α] [IsSemiring α] (n: Nat) (h: n = (0: α)) (g: (∀m: Nat, m = (0: α) -> n ∣ m)) : HasChar α n where
   spec := by
    intro m
    apply Iff.intro
    · intro g'
      apply g
      clear g
      rw [natCast_eq_nsmul_one]
      apply g'
    · rintro ⟨k, rfl⟩
      intro a
      rw [mul_nsmul, nsmul_eq_natCast_mul, h, zero_mul]

instance Nat.char_eq : HasChar Nat 0 := by
  apply HasChar.of_natCast_eq_zero
  rfl
  intro m h
  cases h
  apply Nat.dvd_refl

def char_eq_of_natCast_eq_zero [SemiringOps α] [IsSemiring α] (n: Nat) :
  n = (0: α) -> (∀m: Nat, m = (0: α) -> n ∣ m) -> char α = n := by
  intro h g
  have := HasChar.of_natCast_eq_zero n h g
  apply HasChar.eq α (HasChar.char α) this

def HasChar.natCast_eq_zero [SemiringOps α] [IsSemiring α] [HasChar α n]:
  (n: α) = 0 := by
  rw [natCast_eq_nsmul_one, HasChar.char_spec]

def HasChar.dvd_of_ring_hom
  [SemiringOps α] [IsSemiring α] [SemiringOps β] [IsSemiring β]
  [HasChar α n] [HasChar β m]
  (h: α →+* β) : m ∣ n := by
  apply HasChar.char_dvd (α := β)
  intro b
  rw [←one_mul b, nsmul_eq_natCast_mul, ←mul_assoc, ←nsmul_eq_natCast_mul,
  ←map_one h, ←map_nsmul, char_spec α, map_zero, zero_mul]

def HasChar.eq_of_ring_equiv
  [SemiringOps α] [IsSemiring α] [SemiringOps β] [IsSemiring β]
  [HasChar α n] [HasChar β m]
  (eqv: α ≃+* β) : n = m := by
  apply Nat.dvd_antisymm
  exact dvd_of_ring_hom eqv.symm.toHom
  exact dvd_of_ring_hom eqv.toHom

def HasChar.of_ring_emb
  [SemiringOps α] [IsSemiring α] [SemiringOps β] [IsSemiring β]
  [HasChar α n]
  (emb: α ↪+* β) : HasChar β n := by
  apply HasChar.of_natCast_eq_zero
  · rw [←map_zero emb, ←HasChar.natCast_eq_zero, map_natCast]
  · intro m h
    apply HasChar.char_dvd α
    intro x
    apply emb.inj
    show emb _ = emb _
    rw [map_zero, map_nsmul, nsmul_eq_natCast_mul, h, zero_mul]

def HasChar.of_ring_equiv
  [SemiringOps α] [IsSemiring α] [SemiringOps β] [IsSemiring β]
  [HasChar β n]
  (eqv: α ≃+* β) : HasChar α n := by
  apply HasChar.of_ring_emb (eqv.symm: β ↪+* _)

def char_dvd_char (α β: Type*)
   [SemiringOps α] [IsSemiring α] [SemiringOps β] [IsSemiring β]
   (h: α →+* β) : char β ∣ char α := by
   have := HasChar.char α
   have := HasChar.char β
   exact HasChar.dvd_of_ring_hom h

def char_eq_char_of_eqv (α β: Type*)
   [SemiringOps α] [IsSemiring α] [SemiringOps β] [IsSemiring β]
   (eqv: α ≃+* β) : char α = char β := by
   have := HasChar.char α
   have := HasChar.char β
   exact HasChar.eq_of_ring_equiv eqv

def HasChar.char_dvd_natCast_eq_zero [SemiringOps α] [IsSemiring α] [HasChar α n]
  (m: ℕ) (h: (m: α) = 0): n ∣ m := by
  apply char_dvd (α := α)
  intro x
  rw [nsmul_eq_natCast_mul, h, zero_mul]

def HasChar.natCast_inj [SemiringOps α] [IsSemiring α] [IsAddCancel α] [HasChar α 0]: Function.Injective (fun n: ℕ => (n: α)) := by
  suffices ∀n m: ℕ, (n: α) = m -> n ≤ m -> n = m by
    intro n m eq
    rcases Nat.le_total n m with h | h
    apply this
    assumption
    assumption
    symm; apply this
    symm; assumption
    assumption
  intro n m eq h
  have : ((m - n: ℕ): α) + n = 0 + m := by
    rw [←natCast_add, Nat.sub_add_cancel h, zero_add]
  rw [eq] at this
  have := add_right_cancel this
  have := HasChar.char_dvd_natCast_eq_zero _ this
  have := Nat.zero_dvd.mp this
  have := Nat.le_of_sub_eq_zero this
  apply Nat.le_antisymm <;> assumption

def HasChar.eq_zero_of_add_hom
  [SemiringOps α] [IsSemiring α] [SemiringOps β] [IsSemiring β]
  [HasChar β 0] [IsAddCancel β]
  [FunLike F α β] [IsZeroHom F α β] [IsOneHom F α β] [IsAddHom F α β]
  (f: F) : HasChar α 0 :=
  HasChar.of_ring_emb (α := ℕ) <| {
    toFun n := n
    map_zero := natCast_zero
    map_one := natCast_one
    map_add := natCast_add _ _
    map_mul := natCast_mul _ _
    inj' := by
      intro a b h
      replace h : (a : α) = (b: α) := h
      have : f (a: α) = f (b: α) := by rw [h]
      rw [map_natCast, map_natCast] at this
      exact HasChar.natCast_inj this
  }
