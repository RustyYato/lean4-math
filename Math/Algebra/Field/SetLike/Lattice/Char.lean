import Math.Algebra.Field.SetLike.Lattice
import Math.Algebra.Field.SetLike.Basic
import Math.Algebra.QAlgebra.Basic
import Math.Data.Rat.Basic
import Math.Algebra.Field.Impls.Fin
import Math.AxiomBlame

-- TODO: prove that for `HasChar α 0`, `⊥: α ≃+* ℚ`
-- and for `HasChar α (n + 1)`, `⊥: α ≃+* Fin (n + 1)`

private def field_char' (F: Type*) [SemiringOps F] [IsSemiring F] [IsNontrivial F] [NoZeroDivisors F] [HasChar F n] (h: n ≠ 0) : Nat.IsPrime n := by
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

-- the characteristic of any semifield is 0 or a prime number
-- for example, ℚ has characteristic 0, and any finite field has a prime characteristic
def field_char (F: Type*) [SemiringOps F] [IsSemiring F] [IsNontrivial F] [NoZeroDivisors F] [HasChar F n] : n = 0 ∨ Nat.IsPrime n := by
  apply Decidable.or_iff_not_imp_left.mpr
  apply field_char' F

variable (F: Type*) [FieldOps F] [IsField F]

section

variable [HasChar F 0]

local instance : RatCast F where
  ratCast := ratCastRec

local instance : SMul ℚ F where
  smul r x := r * x

local instance : QAlgebraOps F where
local instance : IsQAlgebra F where
  ratCast_eq_ratCastRec _ := rfl

def has_char_zero_bij_rat : ℚ ⇔+* (⊥: Subfield F) where
  toFun a := ⟨a, by
    rw [ratCast_eq_ratCastRec]
    induction a using Rat.ind with | mk a =>
    show _ /? _ ~(_) ∈ _
    rw [div?_eq_mul_inv?]
    apply mem_mul
    apply mem_intCast
    apply mem_inv?
    apply mem_natCast⟩
  map_zero := by
    congr; rw [ratCast_zero]
  map_one := by
    congr; rw [ratCast_one]
  map_add {_ _} := by
    congr
    show Rat.castHom _ = Rat.castHom _ + Rat.castHom _
    rw [map_add]
  map_mul {_ _} := by
    congr
    show Rat.castHom _ = Rat.castHom _ * Rat.castHom _
    rw [map_mul]
  inj' := by
    intro x y h
    exact ratCast_inj (Subtype.mk.inj h)
  surj' := by
    intro ⟨x, hx⟩
    rw [Subfield.mem_bot_iff] at hx
    obtain ⟨⟨n, d⟩, hd, h⟩ := hx
    exists (Rat.mk ⟨n, d, Nat.pos_of_ne_zero (by
      dsimp at hd
      rwa [←natCast_zero, HasChar.natCast_inj.eq_iff] at hd)⟩)
    congr

noncomputable def has_char_zero_equiv_rat : ℚ ≃+* (⊥: Subfield F) := {
  Bijection.toEquiv (has_char_zero_bij_rat F).toBijection, has_char_zero_bij_rat F with
}

end

section

variable [HasChar F n] [NeZero n]

private def n_prime : Nat.IsPrime n := by
  rcases (field_char F) with rfl | h
  rename_i h; exact (h.out rfl).elim
  assumption

-- instance : IsPrimeClass n where
--   proof := n_prime F

def Subfield.ofFinCast : Subfield F :=
  have : Nat.IsPrimeClass n := ⟨n_prime F⟩
  Subfield.range (F := _ →+* _) (α := Fin n) <| {
    toFun a := a.val
    map_zero := by apply natCast_zero
    map_one := by
      rename_i h
      match n, h with
      | n + 2, h =>
      apply natCast_one
    map_add {a b} := by
      show (Fin.val (Fin.mk _ _): F) = _
      simp
      rw [←natCast_add, ←Nat.div_add_mod (a.val + b.val) n, natCast_add,
        natCast_mul, HasChar.natCast_eq_zero (n := n)]
      simp
    map_mul {a b} := by
      show (Fin.val (Fin.mk _ _): F) = _
      simp
      rw [←natCast_mul, ←Nat.div_add_mod (a.val * b.val) n, natCast_add,
        natCast_mul, HasChar.natCast_eq_zero (n := n)]
      simp
  }

def Subfield.ofFinCast_eq_bot : Subfield.ofFinCast F = ⊥ := by
  apply flip le_antisymm
  apply bot_le
  rintro _ ⟨x, rfl⟩
  simp
  show (x.val: F) ∈ ⊥
  rw [mem_bot_iff]
  refine ⟨⟨x.val, 1⟩, ?_, ?_⟩
  simp; exact (zero_ne_one _).symm
  simp [natCast_one, intCast_ofNat]

noncomputable def has_char_prime_equiv_fin : Fin n ≃+* (⊥: Subfield F) := by
  apply RingEquiv.trans _ (Subfield.equiv_of_eq (Subfield.ofFinCast F) ⊥ (Subfield.ofFinCast_eq_bot F))
  have : Nat.IsPrimeClass n := ⟨n_prime F⟩
  apply Subfield.equiv_range

end
