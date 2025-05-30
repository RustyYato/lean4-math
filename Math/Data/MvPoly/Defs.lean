import Math.Algebra.Monoid.MonoidAlgebra
import Math.Algebra.GroupWithZero.Defs
import Math.Data.Finsupp.Fintype

abbrev MvPoly.Vars (σ: Type*) :=
  AddMonoidAlgebra σ ℕ (LazyFinset σ)

def MvPoly (P σ: Type*) [Zero P] := AddMonoidAlgebra (MvPoly.Vars σ) P (LazyFinset (MvPoly.Vars σ))

namespace MvPoly

variable [Zero P]

instance : Zero (MvPoly P σ) :=
  inferInstanceAs (Zero (AddMonoidAlgebra _ _ _))

instance [DecidableEq P] : DecidableEq (MvPoly P σ) :=
  inferInstanceAs (DecidableEq (AddMonoidAlgebra _ _ _))

def toAddMonoidAlgebra : MvPoly P σ -> AddMonoidAlgebra (MvPoly.Vars σ) P (LazyFinset (MvPoly.Vars σ)) := id

def coeff (p: MvPoly P σ) : Vars σ -> P := p.toAddMonoidAlgebra

@[simp]
def apply_toAddMonoidAlgebra (p: MvPoly P σ) : p.toAddMonoidAlgebra x = p.coeff x := rfl

@[ext]
def ext (a b: MvPoly P σ) : (∀v, a.coeff v = b.coeff v) -> a = b := AddMonoidAlgebra.ext _ _

@[simp]
def coeff_zero (v: Vars σ) :  coeff 0 v = 0 := rfl

end MvPoly

namespace MvPoly

instance [SemiringOps P] [IsSemiring P] : Add (MvPoly P σ) :=
  inferInstanceAs (Add (AddMonoidAlgebra _ _ _))
instance [SemiringOps P] [IsSemiring P] : SMul ℕ (MvPoly P σ) :=
  inferInstanceAs (SMul ℕ (AddMonoidAlgebra _ _ _))
instance [SemiringOps P] [IsSemiring P] : IsAddMonoid (MvPoly P σ) :=
  inferInstanceAs (IsAddMonoid (AddMonoidAlgebra _ _ _))

instance [RingOps P] [IsRing P] : Sub (MvPoly P σ) :=
  inferInstanceAs (Sub (AddMonoidAlgebra _ _ _))
instance [RingOps P] [IsRing P] : Neg (MvPoly P σ) :=
  inferInstanceAs (Neg (AddMonoidAlgebra _ _ _))
instance [RingOps P] [IsRing P] : SMul ℤ (MvPoly P σ) :=
  inferInstanceAs (SMul ℤ (AddMonoidAlgebra _ _ _))
instance instIsAddGroup [RingOps P] [IsRing P] : IsAddGroup (MvPoly P σ) :=
  inferInstanceAs (IsAddGroup (AddMonoidAlgebra _ _ _))

instance [SemiringOps P] [IsSemiring P] : Mul (MvPoly P σ) :=
  inferInstanceAs (Mul (AddMonoidAlgebra (MvPoly.Vars σ) P (LazyFinset (MvPoly.Vars σ))))
instance [SemiringOps P] [IsSemiring P] : IsSemigroup (MvPoly P σ) :=
  inferInstanceAs (IsSemigroup (AddMonoidAlgebra _ _ _))
instance [SemiringOps P] [IsSemiring P] : IsNonUnitalNonAssocSemiring (MvPoly P σ) :=
  inferInstanceAs (IsNonUnitalNonAssocSemiring (AddMonoidAlgebra _ _ _))
instance [SemiringOps P] [IsSemiring P] [IsCommMagma P] : IsCommMagma (MvPoly P σ) :=
  inferInstanceAs (IsCommMagma (AddMonoidAlgebra _ _ _))

instance [SemiringOps P] [IsSemiring P] : One (MvPoly P σ) where
  one := AddMonoidAlgebra.single 0 1
instance [SemiringOps P] [IsSemiring P] : Pow (MvPoly P σ) ℕ :=
  instNPowrec
instance [SemiringOps P] [IsSemiring P] : IsMonoid (MvPoly P σ) where
  one_mul a := by
    unfold MvPoly at a
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
    unfold MvPoly at a
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
def C [SemiringOps P] [IsSemiring P] : P ↪+* (MvPoly P σ) where
  toFun := AddMonoidAlgebra.single 0
  inj' := AddMonoidAlgebra.single_inj
  map_zero := AddMonoidAlgebra.single_zero _
  map_add := (AddMonoidAlgebra.single_add _ _ _).symm
  map_one := rfl
  map_mul {x y} := by rw [AddMonoidAlgebra.single_mul, add_zero]
def monomial [Zero P] [One P] : Vars σ -> (MvPoly P σ) :=
  (AddMonoidAlgebra.single · 1)

variable [DecidableEq σ]

def X [Zero P] [One P] (v: σ) : (MvPoly P σ) :=
  monomial (AddMonoidAlgebra.single v 1)

def X_mul_eq_mul_X [SemiringOps P] [IsSemiring P] (p: MvPoly P σ) (i: σ) : X i * p = p * X i := by
  show AddMonoidAlgebra.mul' _ _ = AddMonoidAlgebra.mul' _ _
  unfold AddMonoidAlgebra.mul' X monomial
  conv => { lhs; arg 1; rw [AddMonoidAlgebra.single_toFinsupp] }
  conv => { rhs; lhs;intro i a; conv => { arg 1; rw [AddMonoidAlgebra.single_toFinsupp] }; rw [Finsupp.single_sum] }
  rw [Finsupp.single_sum]
  congr; ext; congr 2
  rw [add_comm]
  simp
def Xpow_mul_eq_mul_Xpow [SemiringOps P] [IsSemiring P] (p: MvPoly P σ) (i: σ) (n: Nat) : X i ^ n * p = p * X i ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [npow_succ, mul_assoc, X_mul_eq_mul_X, ←mul_assoc, ih, mul_assoc]

def erase [Zero P] (p: MvPoly P σ) (n: Vars σ) : MvPoly P σ := AddMonoidAlgebra.erase p n

def x_npow_eq [SemiringOps P] [IsSemiring P] (i: σ) : (X i: MvPoly P σ) ^ n = monomial (AddMonoidAlgebra.single i n) := by
  induction n with
  | zero =>
    rw [npow_zero, AddMonoidAlgebra.single_zero]
    rfl
  | succ n ih =>
    rw [npow_succ', ih, X]; unfold monomial
    rw [AddMonoidAlgebra.single_mul, AddMonoidAlgebra.single_add]
    simp
    rw [Nat.add_comm]

private def apply_x_pow [SemiringOps P] [IsSemiring P] (i: σ) (m: Vars σ) (n: ℕ) : ((X i: MvPoly P σ) ^ n).coeff m = if m = AddMonoidAlgebra.single i n then 1 else 0 := by
  rw [x_npow_eq]
  rfl

private def apply_C [SemiringOps P] [IsSemiring P] (v: Vars σ) : (C x: MvPoly P σ).coeff v = if v = 0 then x else 0 := by
  rfl

private def apply_monomial [SemiringOps P] [IsSemiring P] (x: P) (i: σ) (n m: ℕ) : (C x * X i ^ n: MvPoly P σ).coeff (AddMonoidAlgebra.single i m) = if m = n then x else 0 := by
  rw [AddMonoidAlgebra.mul_def, AddMonoidAlgebra.mul']
  erw [Finsupp.single_sum, x_npow_eq, Finsupp.single_sum]
  simp
  erw [coeff, AddMonoidAlgebra.apply_single]
  symm; split <;> rename_i h; subst m
  simp
  rw [if_neg]
  intro g; apply h; clear h
  have : AddMonoidAlgebra.single (S := LazyFinset σ) i m i = AddMonoidAlgebra.single (S := LazyFinset σ) i n i := by rw [g]
  simpa [AddMonoidAlgebra.apply_single] using this

@[induction_eliminator]
def induction
  [SemiringOps P] [IsSemiring P]
  {motive: MvPoly P σ -> Prop}
  (C: ∀a, motive (C a))
  (x_mul: ∀(i: σ) (a: MvPoly P σ), motive a -> motive (X i * a))
  (add: ∀a b: MvPoly P σ, motive a -> motive b -> motive (a + b))
  (p: MvPoly P σ): motive p := by
  induction p using AddMonoidAlgebra.induction with
  | zero =>
    rw [←map_zero MvPoly.C]
    apply C
  | single_add v p a h ha =>
    apply add _ _ _ ha
    clear ha a
    induction v using AddMonoidAlgebra.induction with
    | zero => apply C
    | single_add i n a g ha =>
      rw [←one_mul p, ←AddMonoidAlgebra.single_mul,
        ←monomial, ←x_npow_eq]
      clear g
      let b : MvPoly P σ := AddMonoidAlgebra.single a p
      let x: MvPoly P σ := X i ^ n
      show motive (x * b)
      unfold x; clear x
      replace ha : motive b := ha
      induction n with
      | zero => rwa [npow_zero, one_mul]
      | succ n ih =>
        rw [npow_succ', mul_assoc]
        apply x_mul
        assumption

def alg_induction [SemiringOps P] [IsSemiring P] {motive: MvPoly P σ -> Prop}
  (C: ∀x, motive (C x))
  (X: ∀i, motive (X i))
  (add: ∀a b: MvPoly P σ, motive a -> motive b -> motive (a + b))
  (mul: ∀a b: MvPoly P σ, motive a -> motive b -> motive (a * b)): ∀p, motive p := by
  intro p
  induction p with
  | C => apply C
  | x_mul i a h =>
    apply mul
    apply X
    assumption
  | add =>
    apply add
    assumption
    assumption

instance [SemiringOps P] [IsSemiring P] : NatCast (MvPoly P σ) where
  natCast n := C n
instance [RingOps P] [IsRing P] : IntCast (MvPoly P σ) where
  intCast n := C n

instance instIsAddMonoidWithOne [SemiringOps P] [IsSemiring P] : IsAddMonoidWithOne (MvPoly P σ) where
  natCast_zero := by
    show C (Nat.cast 0) = 0
    rw [natCast_zero, map_zero]
  natCast_succ n := by
    show C _ = _
    rw [natCast_succ, map_add, map_one]
    rfl

instance instIsAddGroupWithOne [RingOps P] [IsRing P] : IsAddGroupWithOne (MvPoly P σ) := {
  instIsAddMonoidWithOne, instIsAddGroup with
  intCast_ofNat n := by
    show C _ = C _
    rw [intCast_ofNat]
  intCast_negSucc n := by
    show C _ = -C _
    rw [intCast_negSucc, map_neg]
}

instance [SemiringOps P] [IsSemiring P] : IsSemiring (MvPoly P σ) := IsSemiring.inst
instance [RingOps P] [IsRing P] : IsRing (MvPoly P σ) := IsRing.inst

instance [SemiringOps P] [IsSemiring P] : SMul P (MvPoly P σ) :=
  inferInstanceAs (SMul P (AddMonoidAlgebra _ _ _))
instance [SemiringOps P] [IsSemiring P] : IsModule P (MvPoly P σ) :=
  inferInstanceAs (IsModule P (AddMonoidAlgebra _ _ _))

def smul_eq_C_mul [SemiringOps P] [IsSemiring P] (r: P) (p: MvPoly P σ) : r • p = C r * p := by
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
  simp
  erw [Finsupp.sum_apply_single (g := g)]
  rfl

instance [SemiringOps P] [IsSemiring P] : AlgebraMap P (MvPoly P σ) := ⟨C.toRingHom⟩
instance [SemiringOps P] [IsSemiring P] [IsCommMagma P] : IsAlgebra P (MvPoly P σ) where
  commutes := by
    intro r x
    rw [mul_comm]
  smul_def := smul_eq_C_mul

end MvPoly
