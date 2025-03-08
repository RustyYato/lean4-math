import Math.Algebra.Monoid.MonoidAlgebra

def Poly (P: Type*) [Zero P] := AddMonoidAlgebra ℕ P ℕ

namespace Poly

scoped notation:9000 P "[X]" => Poly P

instance [Zero P] : Zero P[X] :=
  inferInstanceAs (Zero (AddMonoidAlgebra _ _ _))
instance [SemiringOps P] [IsSemiring P] : Add P[X] :=
  inferInstanceAs (Add (AddMonoidAlgebra _ _ _))
instance [SemiringOps P] [IsSemiring P] : SMul ℕ P[X] :=
  inferInstanceAs (SMul ℕ (AddMonoidAlgebra _ _ _))
instance [SemiringOps P] [IsSemiring P] : IsAddMonoid P[X] :=
  inferInstanceAs (IsAddMonoid (AddMonoidAlgebra _ _ _))

instance [RingOps P] [IsRing P] : Sub P[X] :=
  inferInstanceAs (Sub (AddMonoidAlgebra _ _ _))
instance [RingOps P] [IsRing P] : Neg P[X] :=
  inferInstanceAs (Neg (AddMonoidAlgebra _ _ _))
instance [RingOps P] [IsRing P] : SMul ℤ P[X] :=
  inferInstanceAs (SMul ℤ (AddMonoidAlgebra _ _ _))
instance instIsAddGroup [RingOps P] [IsRing P] : IsAddGroup P[X] :=
  inferInstanceAs (IsAddGroup (AddMonoidAlgebra _ _ _))

instance [SemiringOps P] [IsSemiring P] : Mul P[X] :=
  inferInstanceAs (Mul (AddMonoidAlgebra _ _ _))
instance [SemiringOps P] [IsSemiring P] : IsSemigroup P[X] :=
  inferInstanceAs (IsSemigroup (AddMonoidAlgebra _ _ _))
instance [SemiringOps P] [IsSemiring P] : IsNonUnitalNonAssocSemiring P[X] :=
  inferInstanceAs (IsNonUnitalNonAssocSemiring (AddMonoidAlgebra _ _ _))
instance [SemiringOps P] [IsSemiring P] [IsCommMagma P] : IsCommMagma P[X] :=
  inferInstanceAs (IsCommMagma (AddMonoidAlgebra _ _ _))

instance [SemiringOps P] [IsSemiring P] : One P[X] where
  one := AddMonoidAlgebra.single 0 1
instance [SemiringOps P] [IsSemiring P] : MonoidOps P[X] := ⟨flip npowRec⟩
instance [SemiringOps P] [IsSemiring P] : IsMonoid P[X] where
  one_mul a := by
    unfold Poly at a
    show AddMonoidAlgebra.single 0 1 * a = _
    rw [AddMonoidAlgebra.mul_def, AddMonoidAlgebra.mul']
    conv => { lhs; arg 1; rw [AddMonoidAlgebra.single_toFinsupp] }
    rw [Finsupp.single_sum]
    conv => { lhs; arg 2; intro j b; rw [zero_add, one_mul] }
    unfold AddMonoidAlgebra.single
    apply AddMonoidAlgebra.toFinsupp_inj
    rw [AddMonoidAlgebra.sum_toFinsupp]
    rw [Finsupp.sum_single]
  mul_one a := by
    unfold Poly at a
    show a * AddMonoidAlgebra.single 0 1 = _
    rw [AddMonoidAlgebra.mul_def, AddMonoidAlgebra.mul']
    conv => {
      lhs; arg 2; intro j b
      conv => {
        arg 1; rw [AddMonoidAlgebra.single_toFinsupp]
      }
      rw [Finsupp.single_sum] }
    conv => { lhs; arg 2; intro j b; rw [add_zero, mul_one] }
    unfold AddMonoidAlgebra.single
    apply AddMonoidAlgebra.toFinsupp_inj
    rw [AddMonoidAlgebra.sum_toFinsupp]
    rw [Finsupp.sum_single]

-- the canonical embedding from the ambient semiring into the polynomial
def C [SemiringOps P] [IsSemiring P] : P ↪+* P[X] where
  toFun := AddMonoidAlgebra.single 0
  inj' := AddMonoidAlgebra.single_inj
  resp_zero := AddMonoidAlgebra.single_zero _
  resp_add := (AddMonoidAlgebra.single_add _ _ _).symm
  resp_one := rfl
  resp_mul {x y} := by
    dsimp
    rw [AddMonoidAlgebra.single_mul, add_zero]

def monomial [Zero P] [One P] : ℕ -> P[X] :=
  (AddMonoidAlgebra.single · 1)

def X [Zero P] [One P] : P[X] :=
  monomial 1

def X_mul_eq_mul_X [SemiringOps P] [IsSemiring P] (p: P[X]) : X * p = p * X := by
  show AddMonoidAlgebra.mul' _ _ = AddMonoidAlgebra.mul' _ _
  unfold AddMonoidAlgebra.mul' X monomial
  conv => { lhs; arg 1; rw [AddMonoidAlgebra.single_toFinsupp] }
  conv => { rhs; lhs;intro i a; conv => { arg 1; rw [AddMonoidAlgebra.single_toFinsupp] }; rw [Finsupp.single_sum] }
  rw [Finsupp.single_sum]
  congr; ext; congr 2
  rw [add_comm]
  simp

def erase [Zero P] (p: P[X]) (n: ℕ) : P[X] := AddMonoidAlgebra.erase p n

def x_npow_eq [SemiringOps P] [IsSemiring P] : (X ^ n: P[X]) = monomial n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [npow_succ, ih, monomial, X, monomial, AddMonoidAlgebra.single_mul, mul_one]
    rfl

private def apply_x_pow [SemiringOps P] [IsSemiring P] (i n: ℕ) : (X ^ n: P[X]).toFinsupp i = if i = n then 1 else 0 := by
  rw [x_npow_eq]
  rfl

private def apply_C_zero [SemiringOps P] [IsSemiring P] : (C x: P[X]).toFinsupp 0 = x := by
  rfl
private def apply_C_succ [SemiringOps P] [IsSemiring P] (n: ℕ) : (C x: P[X]).toFinsupp (n + 1) = 0 := by
  rfl

private def apply_monomial [SemiringOps P] [IsSemiring P] (x: P) (n i: ℕ) : (C x * X ^ n: P[X]).toFinsupp i = if i = n then x else 0 := by
  rw [AddMonoidAlgebra.mul_def, AddMonoidAlgebra.mul']
  rw [←AddMonoidAlgebra.applyHom_eq]
  show AddMonoidAlgebra.applyHom i _ = _
  simp [Finsupp.resp_sum]
  show (Finsupp.single _ _).sum _ _ = _
  rw [Finsupp.single_sum]
  rw [x_npow_eq]
  show (Finsupp.single _ _).sum _ _ = _
  rw [Finsupp.single_sum]
  rw [zero_add, mul_one]
  show (AddMonoidAlgebra.single _ _) i = _
  rw [AddMonoidAlgebra.apply_single]

@[induction_eliminator]
def induction
  [SemiringOps P] [IsSemiring P]
  {motive: P[X] -> Prop}
  (C: ∀a, motive (C a))
  (monomial: ∀r: P, ∀n: ℕ, motive (.C r * X ^ n) -> motive (.C r * X ^ (n + 1)))
  (add: ∀a b: P[X], motive a -> motive b -> motive (a + b))
  (p: P[X]): motive p := by
  unfold Poly at p
  induction p.toFinsupp.spec with | mk spec =>
  obtain ⟨degree, spec⟩ := spec
  induction degree generalizing p with
  | zero =>
    suffices p = Poly.C 0 by
      rw [this]
      apply C
    ext n
    rw [resp_zero]
    show p n = 0
    apply Classical.byContradiction
    intro h
    have := spec _ h
    contradiction
  | succ n ih =>
    suffices p = erase p n + Poly.C (p.toFinsupp n) * X ^ n by
      rw [this]; clear this
      apply add
      apply ih
      · intro x h
        unfold erase AddMonoidAlgebra.erase Finsupp.erase at h
        simp at h
        obtain ⟨x_ne_n, h⟩ := h
        have := spec _ h
        rw [Nat.mem_iff_lt] at *
        exact lt_of_le_of_ne (Nat.le_of_lt_succ this) x_ne_n
      clear spec ih
      generalize p.toFinsupp n = p'
      induction n with
      | zero =>
        rw [npow_zero, mul_one]
        apply C
      | succ n ih =>
        apply monomial
        assumption
    ext i
    show _ = (erase p n).toFinsupp i + _
    rw [apply_monomial]
    show _ = (if _ then _ else _) + _
    split
    rw [zero_add]; subst i; rfl
    rw [add_zero]; rfl

instance [SemiringOps P] [IsSemiring P] : NatCast P[X] where
  natCast n := C n
instance [SemiringOps P] [IsSemiring P] : OfNat P[X] (n+2) where
  ofNat := C (OfNat.ofNat (n+2))
instance [RingOps P] [IsRing P] : IntCast P[X] where
  intCast n := C n

instance instIsAddMonoidWithOne [SemiringOps P] [IsSemiring P] : IsAddMonoidWithOne P[X] where
  natCast_zero := by
    show C (Nat.cast 0) = 0
    rw [natCast_zero, resp_zero]
  natCast_succ n := by
    show C _ = _
    rw [natCast_succ, resp_add, resp_one]
    rfl
  ofNat_eq_natCast n := by
    show C _ = C _
    rw [ofNat_eq_natCast]

instance instIsAddGroupWithOne [RingOps P] [IsRing P] : IsAddGroupWithOne P[X] := {
  instIsAddMonoidWithOne, instIsAddGroup with
  intCast_ofNat n := by
    show C _ = C _
    rw [intCast_ofNat]
  intCast_negSucc n := by
    show C _ = -C _
    rw [intCast_negSucc, resp_neg]
}

instance [RingOps P] [IsRing P] : IsRing P[X] := {
  instIsAddGroupWithOne with
}

end Poly
