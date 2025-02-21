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
  ←resp_one h, ←resp_nsmul, char_spec α, resp_zero, zero_mul]

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
  · rw [←resp_zero emb, ←HasChar.natCast_eq_zero, resp_natCast]
  · intro m h
    apply HasChar.char_dvd α
    intro x
    apply emb.inj
    show emb _ = emb _
    rw [resp_zero, resp_nsmul, nsmul_eq_natCast_mul, h, zero_mul]

def HasChar.of_ring_equiv
  [SemiringOps α] [IsSemiring α] [SemiringOps β] [IsSemiring β]
  [HasChar β n]
  (eqv: α ≃+* β) : HasChar α n := by
  apply HasChar.of_ring_emb eqv.symm.toEmbedding

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

instance Nat.char_eq : HasChar Nat 0 := by
  apply HasChar.of_natCast_eq_zero
  rfl
  intro m h
  cases h
  apply Nat.dvd_refl
