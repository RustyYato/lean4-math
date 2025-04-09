import Math.Algebra.Semigroup.Impls.Fin
import Math.Algebra.Monoid.Defs
import Math.Algebra.Monoid.Char

variable (n: ℕ) [NeZero n]

instance : SMul ℕ (Fin n) where
  smul m x := ⟨(m * x) % n, Nat.mod_lt _ x.pos⟩
instance : Pow (Fin n) ℕ where
  pow x m := ⟨(x ^ m) % n, Nat.mod_lt _ x.pos⟩

instance Fin.instIsAddMonoid : IsAddMonoid (Fin n) where
  zero_nsmul _ := by
    show Fin.mk _ _ = Fin.mk _ _
    simp
  succ_nsmul := by
    intro m a
    show Fin.mk _ _ = Fin.mk _ _
    simp
    rw [Nat.add_mul, Nat.one_mul]

instance Fin.instIsMonoid : IsMonoid (Fin n) where
  npow_zero _ := rfl
  npow_succ := by
    intro a m
    show Fin.mk _ _ = Fin.mk _ _
    simp
    rw [Nat.pow_succ]

instance : HasChar (Fin n) n := by
  rename_i h
  match n, h with
  | 1, h => infer_instance
  | n + 2, h =>
  apply HasChar.of_spec
  · intro a
    show Fin.mk _ _ = Fin.mk 0 _
    simp
  · intro m meq
    refine Nat.dvd_of_mod_eq_zero ?_
    have : Fin.mk _ _ = Fin.mk _ _ := meq 1
    simpa using this
