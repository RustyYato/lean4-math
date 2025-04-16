import Math.Algebra.Monoid.MonoidAlgebra
import Math.Algebra.GroupWithZero.Defs
import Math.Data.Finsupp.Fintype

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
  map_zero := AddMonoidAlgebra.single_zero _
  map_add := (AddMonoidAlgebra.single_add _ _ _).symm
  map_one := rfl
  map_mul {x y} := by rw [AddMonoidAlgebra.single_mul, add_zero]

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

def Xpow_mul_eq_mul_Xpow [SemiringOps P] [IsSemiring P] (p: P[X]) (n: Nat) : X ^ n * p = p * X ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [npow_succ, mul_assoc, X_mul_eq_mul_X, ←mul_assoc, ih, mul_assoc]

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
  simp [Finsupp.map_sum]
  show (Finsupp.single _ _).sum _ _ = _
  rw [Finsupp.single_sum]
  rw [x_npow_eq]
  show (Finsupp.single _ _).sum _ _ = _
  rw [Finsupp.single_sum]
  rw [zero_add, mul_one]
  show (AddMonoidAlgebra.single _ _) i = _
  rw [AddMonoidAlgebra.apply_single]

def addmonoid_single_eq [SemiringOps P] [IsSemiring P] : (AddMonoidAlgebra.single n a) = (C a * X ^ n: P[X]) := by
  rw [←mul_one a, ←zero_add n, ←AddMonoidAlgebra.single_mul, x_npow_eq]
  simp; rfl

@[induction_eliminator]
def induction
  [SemiringOps P] [IsSemiring P]
  {motive: P[X] -> Prop}
  (C: ∀a, motive (C a))
  (monomial: ∀r: P, ∀n: ℕ, motive (.C r * X ^ n) -> motive (.C r * X ^ (n + 1)))
  (add: ∀a b: P[X], motive a -> motive b -> motive (a + b))
  (p: P[X]): motive p := by
  induction p using AddMonoidAlgebra.induction with
  | zero =>
    rw [←map_zero Poly.C]
    apply C
  | single_add n p c ne h =>
    apply add
    · rw [addmonoid_single_eq]
      induction n with
      | zero =>
        rw [npow_zero, mul_one]
        apply C
      | succ n ih =>
        apply monomial
        assumption
    · assumption

def alg_induction [SemiringOps P] [IsSemiring P] {motive: P[X] -> Prop}
  (C: ∀x, motive (C x))
  (X: motive X)
  (add: ∀a b: P[X], motive a -> motive b -> motive (a + b))
  (mul: ∀a b: P[X], motive a -> motive b -> motive (a * b)): ∀p, motive p := by
  intro p
  induction p with
  | C => apply C
  | monomial =>
    rw [npow_succ, ←mul_assoc]
    apply mul
    assumption
    apply X
  | add =>
    apply add
    assumption
    assumption

instance [SemiringOps P] [IsSemiring P] : NatCast P[X] where
  natCast n := C n
instance [RingOps P] [IsRing P] : IntCast P[X] where
  intCast n := C n

instance instIsAddMonoidWithOne [SemiringOps P] [IsSemiring P] : IsAddMonoidWithOne P[X] where
  natCast_zero := by
    show C (Nat.cast 0) = 0
    rw [natCast_zero, map_zero]
  natCast_succ n := by
    show C _ = _
    rw [natCast_succ, map_add, map_one]
    rfl

instance instIsAddGroupWithOne [RingOps P] [IsRing P] : IsAddGroupWithOne P[X] := {
  instIsAddMonoidWithOne, instIsAddGroup with
  intCast_ofNat n := by
    show C _ = C _
    rw [intCast_ofNat]
  intCast_negSucc n := by
    show C _ = -C _
    rw [intCast_negSucc, map_neg]
}

instance [SemiringOps P] [IsSemiring P] : IsSemiring P[X] := IsSemiring.inst
instance [RingOps P] [IsRing P] : IsRing P[X] := IsRing.inst

instance [SemiringOps P] [IsSemiring P] : SMul P P[X] :=
  inferInstanceAs (SMul P (AddMonoidAlgebra ℕ P ℕ))
instance [SemiringOps P] [IsSemiring P] : IsModule P P[X] :=
  inferInstanceAs (IsModule P (AddMonoidAlgebra ℕ P ℕ))

def smul_eq_C_mul [SemiringOps P] [IsSemiring P] (r: P) (p: P[X]) : r • p = C r * p := by
  rw [AddMonoidAlgebra.mul_def, AddMonoidAlgebra.mul']
  unfold C AddMonoidAlgebra.single
  erw [Finsupp.single_sum]
  show _ = p.toFinsupp.sum _ _
  conv => {
    rhs; arg 2; intro j b; rw [zero_add]
  }
  apply AddMonoidAlgebra.toFinsupp_inj
  ext i
  show r * p.toFinsupp i = _
  rw [AddMonoidAlgebra.sum_toFinsupp (h₁ := by
    intro i eq
    show Finsupp.singleHom _ _ = _
    rw [eq, mul_zero, map_zero])]
  simp
  let g : ZeroHom P P := {
    toFun := (r * ·)
    map_zero := mul_zero _
  }
  show _ = Finsupp.applyHom _ _
  rw [Finsupp.map_sum]
  show r * p.toFinsupp i = p.toFinsupp.sum (fun i₀ a => (Finsupp.single (S := ℕ) i₀ (g a)) i) _
  rw [Finsupp.sum_apply_single]
  rfl

instance [SemiringOps P] [IsSemiring P] : AlgebraMap P P[X] := ⟨C.toRingHom⟩
instance [SemiringOps P] [IsSemiring P] [IsCommMagma P] : IsAlgebra P P[X] where
  commutes := by
    intro r x
    rw [mul_comm]
  smul_def := smul_eq_C_mul

def Xpow_eq_monomial [SemiringOps P] [IsSemiring P] : (X: P[X]) ^ n = monomial n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [npow_succ, ih]
    apply AddMonoidAlgebra.ext
    intro i
    simp [X, monomial]
    rw [AddMonoidAlgebra.single_mul]
    simp [AddMonoidAlgebra.apply_single]

def coeff_mul_Xpow [SemiringOps P] [IsSemiring P] (a: P[X]) (hi: n ≤ i) : (a * X^n).toFinsupp i = a.toFinsupp (i - n) := by
  rw [
    ←Xpow_mul_eq_mul_Xpow,
    Xpow_eq_monomial]
  rw [monomial]
  simp [HMul.hMul, Mul.mul]
  simp [AddMonoidAlgebra.mul']
  rw [Finsupp.single_sum,
    AddMonoidAlgebra.sum_toFinsupp']
  conv => {
    arg 1; arg 2; intro i₀ a
    simp [one_mul, AddMonoidAlgebra.single, Finsupp.apply_single]
    arg 1; rw [Nat.add_comm, ←Nat.sub_eq_iff_eq_add hi, Eq.comm]
  }
  erw [Finsupp.sum_select (g := ZeroHom.mk id rfl)]
  rfl

@[simp]
def coeff_mul_X_zero [SemiringOps P] [IsSemiring P] (a: P[X]) : (a * X).toFinsupp 0 = 0 := by
  rw [←X_mul_eq_mul_X, AddMonoidAlgebra.mul_def, AddMonoidAlgebra.mul']
  erw [Finsupp.single_sum, AddMonoidAlgebra.sum_toFinsupp', Finsupp.sum_eq_zero]
  intro i
  simp [Finsupp.apply_single]
  intro; rw [add_comm] at *; contradiction

@[simp]
def coeff_mul_X_succ [SemiringOps P] [IsSemiring P] (a: P[X]) : (a * X).toFinsupp (i + 1) = a.toFinsupp i := by
  rw [←npow_one X, coeff_mul_Xpow]
  rfl
  apply Nat.le_add_left

@[simp]
def coeff_C_zero [SemiringOps P] [IsSemiring P] (a: P) : (C a).toFinsupp 0 = a := rfl

@[simp]
def coeff_C_succ [SemiringOps P] [IsSemiring P] (a: P) : (C a).toFinsupp (i + 1) = 0 := rfl

@[simp]
def coeff_add [SemiringOps P] [IsSemiring P] (a b: P[X]) : (a + b).toFinsupp i = a.toFinsupp i + b.toFinsupp i := rfl

@[ext]
def ext [Zero P] (a b: P[X]) : (∀x, a.toFinsupp x = b.toFinsupp x) -> a = b := AddMonoidAlgebra.ext _ _

def smul_eq_const_mul [SemiringOps P] [IsSemiring P] [IsCommMagma P] (x: P) (a: P[X]) : x • a = C x * a := by
  rw [smul_def]
  rfl

def mul_X_add_C_inj [RingOps P] [IsRing P] : Function.Injective₂ (fun (a: P[X]) (b: P) => a * X + C b) := by
  intro a b c d eq
  dsimp at eq
  have coeff_eq : ∀i, (a * X + C b).toFinsupp i = (c * X + C d).toFinsupp i := fun i => by rw [eq]
  replace coeff_eq : ∀i, (a * X).toFinsupp i + (C b).toFinsupp i = (c * X).toFinsupp i + (C d).toFinsupp i := coeff_eq
  have := coeff_eq 0
  simp [coeff_mul_X_zero] at this
  cases this
  apply And.intro _ rfl
  ext i
  have := coeff_eq (i + 1)
  simp at this
  assumption

def mul_X_inj [RingOps P] [IsRing P] : Function.Injective (fun (a: P[X]) => a * X) := by
  intro a b eq
  dsimp at eq
  have : a * X + C 0 = b * X + C 0 := by rw [eq]
  exact (mul_X_add_C_inj this).left

def mul_Xpow_inj [RingOps P] [IsRing P] (n: ℕ ) : Function.Injective (fun (a: P[X]) => a * X ^ n) := by
  intro a b h
  induction n with
  | zero => simpa using h
  | succ n ih =>
    simp [npow_succ, ←mul_assoc] at h
    exact ih (mul_X_inj h)

def of_mul_Xpow_eq_zero [RingOps P] [IsRing P] (a: P[X]) (n: Nat) : a * X ^ n = 0 -> a = 0 := by
  intro h
  rw [←zero_mul (X ^ n)] at h
  exact mul_Xpow_inj _ h

def subsingleton_of_monomial_eq_zero [Zero P] [One P] [Mul P] [IsMulZeroClass P] [IsMulOneClass P] (h: (monomial n: P[X]) = 0) : Subsingleton P := by
  apply subsingleton_of_trivial
  symm;
  suffices (monomial n).toFinsupp n = (1: P) by
    rw [←this, h]
    rfl
  unfold monomial
  erw [AddMonoidAlgebra.apply_single, if_pos rfl]

def C_eq_algebraMap [SemiringOps P] [IsSemiring P]  : C x = algebraMap (R := P) x := rfl

end Poly
