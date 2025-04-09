import Math.Algebra.Semigroup.Impls.Prod
import Math.Algebra.Monoid.Defs
import Math.Algebra.Monoid.Char

instance [AddMonoidOps α] [AddMonoidOps β] [IsAddMonoid α] [IsAddMonoid β] : IsAddMonoid (α × β) where
  zero_nsmul := by
    intro f; ext <;>
    apply zero_nsmul
  succ_nsmul := by
    intro n f; ext <;>
    apply succ_nsmul

instance [MonoidOps α] [MonoidOps β] [IsMonoid α] [IsMonoid β] : IsMonoid (α × β)  :=
  inferInstanceAs (IsMonoid (MulOfAdd (AddOfMul α × AddOfMul β)))

instance (priority := 100)
  [AddMonoidOps α] [AddMonoidOps β]
  [IsAddMonoid α] [IsAddMonoid β]
  [HasChar α n] [HasChar β m] : HasChar (α × β) (Nat.lcm n m) := by
  apply HasChar.of_spec
  · intro a
    ext <;> simp
    apply HasChar.nsmul_eq_zero_of_dvd
    exact Nat.dvd_lcm_left n m
    apply HasChar.nsmul_eq_zero_of_dvd
    exact Nat.dvd_lcm_right n m
  · intro k h
    refine Nat.lcm_dvd ?_ ?_
    apply HasChar.char_dvd (α := α)
    intro x
    show k • (x, (0: β)).fst = 0
    rw [←Prod.nsmul_fst, h]
    rfl
    apply HasChar.char_dvd (α := β)
    intro x
    show k • ((0: α), x).snd = 0
    rw [←Prod.nsmul_snd, h]
    rfl

instance
  [AddMonoidOps α] [AddMonoidOps β]
  [IsAddMonoid α] [IsAddMonoid β]
  [HasChar α n] [HasChar β n] : HasChar (α × β) n := by
  rw [←Nat.lcm_self n]
  infer_instance
