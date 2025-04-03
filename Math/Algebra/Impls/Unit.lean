import Math.Algebra.Ring.Defs
import Math.Algebra.Monoid.Char
import Math.Algebra.Basic

instance : RingOps Unit where
  add _ _ := ()
  zero := ()
  one := ()
  natCast _ := ()
  mul _ _ := ()
  neg _ := ()
  sub _ _ := ()
  intCast _ := ()
  nsmul _ _ := ()
  npow _ _ := ()
  zsmul _ _ := ()

instance : IsCommMagma Unit where
  mul_comm _ _ := rfl

instance Unit.instRing : IsRing Unit where
  add_comm _ _ := rfl
  add_assoc _ _ _ := rfl
  zero_add _ := rfl
  add_zero _ := rfl
  natCast_zero := rfl
  natCast_succ _ := rfl
  mul_assoc _ _ _ := rfl
  zero_mul _ := rfl
  mul_zero _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  left_distrib _ _ _ := rfl
  right_distrib _ _ _ := rfl
  sub_eq_add_neg _ _ := rfl
  zsmul_negSucc _ _ := rfl
  zsmul_ofNat _ _ := rfl
  neg_add_cancel _ := rfl
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl

instance : IsSemiring Unit := Unit.instRing.toIsSemiring

instance : HasChar Unit 1 := by
  apply HasChar.of_spec
  intro; rfl
  intros
  apply Nat.one_dvd

-- every module over `Unit` is trivial
instance Unit.subsingleton_of_module
  (R: Type*) [SMul Unit R] [AddMonoidOps R] [IsAddCommMagma R] [IsAddMonoid R] [IsModule Unit R]:
  Subsingleton R where
  allEq := by
    suffices ∀x: R, x = 0 by
      intro a b; rw [this a, this b]
    intro a
    rw [←zero_smul (R := Unit) a, one_smul]

example [Add α] [Zero α] [IsAddZeroClass α] : Unit ↪+ α where
  toFun _ := 0
  inj' _ _ _ := rfl
  map_zero := rfl
  map_add := (add_zero _).symm
