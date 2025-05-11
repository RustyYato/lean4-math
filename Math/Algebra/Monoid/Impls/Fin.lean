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

def Fin.lift {n: ℕ} [NeZero n] { α: Type* } [AddMonoidOps α] [IsAddMonoid α]: { f : ℕ →+ α // f n = 0 } ≃ (Fin n →+ α) :=
  have apply_mod (f: { f : ℕ →+ α // f n = 0 }) (x: ℕ) : f.val (x % n) = f.val x := by
    rw (occs := [2]) [←Nat.div_add_mod x n]
    rw [map_add, mul_comm]
    show _ = f.val ((x / n) • n) + _
    erw [map_nsmul, f.property, nsmul_zero, zero_add]
  {
  toFun f := {
    toFun x := f.val x.val
    map_zero := map_zero f.val
    map_add := by
      intro x y
      rw [←map_add f.val]
      apply apply_mod
  }
  invFun f := {
    val := {
      toFun x := f (Fin.ofNat' n x)
      map_zero := map_zero f
      map_add := by
        intro x y
        rw [←map_add]
        simp [Fin.ofNat']
        rw [Fin.add_def]
        simp
    }
    property := by
      show f (Fin.ofNat' n _) = 0
      simp [map_zero]
  }
  leftInv f := by
    simp; ext x
    apply apply_mod
  rightInv f := by
    simp; ext x
    show f _  = _
    simp
  }
