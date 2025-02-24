import Math.Function.Basic
import Math.Data.Like.Func
import Math.Data.Nat.Find
import Math.Relation.Basic
import Math.Algebra.Ring.Defs
import Math.Data.Fin.Basic
import Math.Algebra.Basic

def Poly.DegreeLe [Zero P] (f: Nat -> P) (bound: Nat) :=
  ∀n > bound, f n = 0

structure Poly (P: Type*) [Zero P] where
  coeffs: Nat -> P
  has_degree: Squash (Σ'bound: Nat, Poly.DegreeLe coeffs bound)

namespace Poly

scoped notation:9000 P "[X]" => Poly P

instance (priority := 100) [Zero P] [OfNat P n] : OfNat P[X] n where
  ofNat := {
    coeffs
    | 0 => OfNat.ofNat n
    | _ + 1 => 0
    has_degree := Squash.mk ⟨0, fun x _ => match x with | _ + 1 => rfl⟩
  }

instance [Zero P] [NatCast P] : NatCast P[X] where
  natCast n := {
    coeffs
    | 0 => (n: P)
    | _ + 1 => 0
    has_degree := Squash.mk ⟨0, fun x _ => match x with | _ + 1 => rfl⟩
  }

instance [Zero P] [IntCast P] : IntCast P[X] where
  intCast n := {
    coeffs
    | 0 => (n: P)
    | _ + 1 => 0
    has_degree := Squash.mk ⟨0, fun x _ => match x with | _ + 1 => rfl⟩
  }

instance [Zero P] [One P] : One P[X] := ⟨1⟩

instance [Zero P] : Zero P[X] where
  zero := {
    coeffs _ := 0
    has_degree := Squash.mk ⟨0, fun _ _ => rfl⟩
  }

section degree

variable [Zero P] [BEq P] [LawfulBEq P]

private
def findDegree (f: Nat -> P) : (Σ'm: Nat, Poly.DegreeLe f m) -> Σ'm: Nat, Poly.DegreeLe f m ∧ ∀x, Poly.DegreeLe f x -> m ≤ x
| ⟨0, h⟩ => ⟨0, h, fun _ _ => Nat.zero_le _⟩
| ⟨m + 1, hm⟩ => by
  if f (m + 1) == 0 then
    refine Poly.findDegree f ⟨m, ?_⟩
    intro n m_lt_n
    have := hm n
    rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt m_lt_n) with m_lt_n | m_eq_n
    apply hm
    assumption
    subst n
    apply LawfulBEq.eq_of_beq
    assumption
  else
    refine ⟨m+1, hm, ?_⟩
    intro x deg
    apply Decidable.byContradiction
    intro g
    replace g := Nat.lt_of_not_le g
    rw [(deg _ g), LawfulBEq.rfl] at *
    contradiction

def degree (p: P[X]) : Nat := by
  apply p.has_degree.liftOn _ _
  intro h
  -- search for the degree starting at the current degree
  -- since we expect that to be a good estimate. This way we
  -- will usually only have to check a single number
  exact (findDegree p.coeffs h).fst
  intro a b _
  generalize Poly.findDegree p.coeffs a = x
  generalize Poly.findDegree p.coeffs b = y
  apply Nat.le_antisymm
  apply x.snd.right
  exact y.snd.left
  apply y.snd.right
  exact x.snd.left

def degree.DegreeLe (p: P[X]) : Poly.DegreeLe p.coeffs p.degree := by
  cases p with
  | mk f h =>
  induction h using Quot.ind with
  | mk h =>
  dsimp
  exact (Poly.findDegree f h).snd.left

def degree_is_minimal (p: P[X]) : ∀x, Poly.DegreeLe p.coeffs x -> p.degree ≤ x := by
  cases p with
  | mk f h =>
  induction h using Quot.ind with
  | mk h =>
  dsimp
  exact (Poly.findDegree f h).snd.right

end degree

def ofCoeffs [Zero P] (coeffs: List P) : P[X] where
  coeffs n := coeffs.getD n 0
  has_degree := by
    refine Squash.mk ⟨coeffs.length, ?_⟩
    intro n h
    dsimp
    unfold List.getD
    rw [List.get?_eq_none]
    rfl
    apply Nat.le_of_lt
    assumption

-- multiply the polynomial by the variable
def mul_var [Zero P] (p: P[X]): P[X] where
  coeffs
  | 0 => 0
  | n + 1 => p.coeffs n
  has_degree := by
    apply p.has_degree.lift
    intro ⟨bound, spec⟩
    apply Squash.mk
    refine ⟨bound + 1, ?_⟩
    intro x h
    match x with
    | x + 1 =>
    apply spec
    apply Nat.lt_of_succ_lt_succ
    assumption

-- divide the polynomial by the variable
def div_var [Zero P] (p: P[X]): P[X] where
  coeffs n := p.coeffs (n + 1)
  has_degree := by
    apply p.has_degree.lift
    intro ⟨bound, spec⟩
    apply Squash.mk
    refine ⟨bound - 1, ?_⟩
    intro x h
    apply spec
    cases bound
    apply Nat.zero_lt_succ
    apply Nat.succ_lt_succ
    assumption

def const [Zero P] (k: P) : P[X] where
  coeffs
  | 0 => k
  | n + 1 => 0
  has_degree := by
    apply Squash.mk
    refine ⟨0, ?_⟩
    intro x lt
    match x with
    | x + 1 =>
    rfl

instance [Zero P] [Add P] [IsAddZeroClass P] : Add P[X] where
  add a b := Poly.mk (fun n => a.coeffs n + b.coeffs n) <| by
    match a, b with
    | .mk a ha, .mk b hb =>
    apply ha.lift
    intro ⟨bound_a, ha⟩
    apply hb.lift
    intro ⟨bound_b, hb⟩
    dsimp
    apply Squash.mk
    refine ⟨max bound_a bound_b, ?_⟩
    intro n h
    dsimp
    rw [ha, hb, add_zero]
    apply Nat.lt_of_le_of_lt _ h
    apply Nat.le_max_right
    apply Nat.lt_of_le_of_lt _ h
    apply Nat.le_max_left

instance [Zero P] [Add P] [Mul P] [IsAddZeroClass P] [IsMulZeroClass P] : Mul P[X] where
  mul a b := Poly.mk (fun n => Fin.sum fun x: Fin (n + 1) => a.coeffs x.val * b.coeffs (n - x.val)) <| by
    match a, b with
    | .mk a ha, .mk b hb =>
    apply ha.lift
    intro ⟨bound_a, ha⟩
    apply hb.lift
    intro ⟨bound_b, hb⟩
    dsimp
    apply Squash.mk
    refine ⟨bound_a + bound_b, ?_⟩
    intro n h
    apply Fin.sum_eq_zero_of_each_eq_zero
    intro x
    if g:bound_a < x then
      rw [ha, zero_mul]
      assumption
    else
      rw [hb, mul_zero]
      apply Nat.add_lt_add_iff_left.mp
      show bound_a + bound_b < _
      apply Nat.lt_of_lt_of_le h
      rw [←Nat.add_sub_assoc, Nat.add_comm, Nat.add_sub_assoc]
      apply Nat.le_add_right
      apply Nat.le_of_not_lt
      assumption
      apply Nat.le_of_lt_succ
      exact x.isLt

instance [Zero P] [Neg P] [IsNegZeroClass P] : Neg P[X] where
  neg p := by
    apply Poly.mk (fun n => -p.coeffs n)
    apply p.has_degree.recOnSubsingleton (motive := fun _ => _)
    intro ⟨bound, spec⟩
    apply Squash.mk
    refine ⟨bound, ?_⟩
    intro n h
    dsimp
    rw [spec, neg_zero]
    assumption

instance [Zero P] [Add P] [SMul ℕ P] [IsAddMonoid P] : SMul ℕ P[X] where
  smul k p := by
    apply Poly.mk (fun n => k • p.coeffs n)
    apply p.has_degree.recOnSubsingleton (motive := fun _ => _)
    intro ⟨bound, spec⟩
    apply Squash.mk
    refine ⟨bound, ?_⟩
    intro n h
    dsimp
    rw [spec, nsmul_zero]
    assumption

instance [Zero P] [Mul P] [IsMulZeroClass P] : SMul P P[X] where
  smul k p := by
    apply Poly.mk (fun n => k * p.coeffs n)
    apply p.has_degree.recOnSubsingleton (motive := fun _ => _)
    intro ⟨bound, spec⟩
    apply Squash.mk
    refine ⟨bound, ?_⟩
    intro n h
    dsimp
    rw [spec, mul_zero]
    assumption

instance [Zero P] [Add P] [Neg P] [Sub P] [SMul ℕ P] [SMul ℤ P] [IsNegZeroClass P] [IsSubNegMonoid P] : SMul ℤ P[X] where
  smul k p := by
    apply Poly.mk (fun n => k • p.coeffs n)
    apply p.has_degree.recOnSubsingleton (motive := fun _ => _)
    intro ⟨bound, spec⟩
    apply Squash.mk
    refine ⟨bound, ?_⟩
    intro n h
    dsimp
    rw [spec, zsmul_zero]
    assumption

instance [Zero P] [Add P] [Neg P] [Sub P] [SMul ℕ P] [SMul ℤ P] [IsNegZeroClass P] [IsSubNegMonoid P] : Sub P[X] where
  sub a b := Poly.mk (fun n => a.coeffs n - b.coeffs n) <| by
    match a, b with
    | .mk a ha, .mk b hb =>
    apply ha.lift
    intro ⟨bound_a, ha⟩
    apply hb.lift
    intro ⟨bound_b, hb⟩
    dsimp
    apply Squash.mk
    refine ⟨max bound_a bound_b, ?_⟩
    intro n h
    dsimp
    rw [ha, hb, sub_zero]
    apply Nat.lt_of_le_of_lt _ h
    apply Nat.le_max_right
    apply Nat.lt_of_le_of_lt _ h
    apply Nat.le_max_left

instance [Zero P] [Neg P] [IsNegZeroClass P] : Neg P[X] where
  neg a := Poly.mk (fun n => -a.coeffs n) <| by
    match a with
    | .mk a ha =>
    apply ha.lift
    intro ⟨bound_a, ha⟩
    dsimp
    apply Squash.mk
    refine ⟨bound_a, ?_⟩
    intro n h
    dsimp
    rw [ha, neg_zero]
    assumption

section

variable [Zero P] [One P] [Add P] [Mul P] [IsAddZeroClass P] [IsMulZeroClass P]

instance [Zero P] [One P] [Add P] [Mul P] [IsAddZeroClass P] [IsMulZeroClass P] : Pow P[X] ℕ := ⟨flip npowRec⟩

def ext_coeffs (a b: P[X]) : a.coeffs = b.coeffs -> a = b := by
  intro h
  cases a;cases b; congr
  apply Subsingleton.helim
  dsimp at h
  rw [h]

def mul_mul_var (p q: P[X]) : p * q.mul_var = (p * q).mul_var := by
  apply ext_coeffs
  ext n
  cases n
  show Fin.sum _ = 0
  rw [Fin.sum_eq_zero_of_each_eq_zero]
  intro a
  erw [Nat.zero_sub, mul_zero]
  unfold mul_var
  show Fin.sum _ = Fin.sum _
  dsimp
  apply Fin.sum_eq_sum_of_prefix
  intro x
  dsimp
  rw [Nat.succ_sub]
  apply Nat.le_of_lt_succ
  · cases x with | mk x xLt =>
    rw [Nat.min_eq_right] at xLt
    assumption
    apply Nat.le_succ
  intro x h
  rw [Nat.sub_eq_zero_iff_le.mpr]
  dsimp
  rw [mul_zero]
  assumption
  intro x h
  have := Nat.lt_asymm x.isLt (Nat.lt_of_succ_le h)
  contradiction

def mul_var_mul (p q: P[X]) : p.mul_var * q = (p * q).mul_var := by
  apply ext_coeffs
  ext n
  cases n
  · show Fin.sum _ = 0
    apply Fin.sum_eq_zero_of_each_eq_zero
    intro x
    match x with
    | ⟨0, _⟩ =>
    erw [zero_mul]
  unfold mul_var
  show Fin.sum _ = Fin.sum _
  dsimp
  rw [Fin.sum]
  dsimp
  rw [zero_mul, zero_add]
  congr
  ext x
  dsimp
  rw [Nat.succ_sub_succ]

instance : IsAddZeroClass P[X] where
  zero_add a := by
    apply Poly.ext_coeffs
    ext n
    show 0 + _ = _
    rw [zero_add]
  add_zero a := by
    apply Poly.ext_coeffs
    ext n
    show _ + 0 = _
    rw [add_zero]

instance [IsAddSemigroup P] : IsAddSemigroup P[X] where
  add_assoc a b c := by
    apply Poly.ext_coeffs
    ext n
    show _ + _ + _ = _
    rw [add_assoc]
    rfl

instance [Neg P] [IsNegZeroClass P] : IsNegZeroClass P[X] where
  neg_zero := by
    apply Poly.ext_coeffs
    ext n
    show - 0 = _
    rw [neg_zero]
    rfl

instance [SMul ℕ P] [IsAddMonoid P] : IsAddMonoid P[X] where
  zero_nsmul p := by
    apply Poly.ext_coeffs
    ext n
    show 0 • (p.coeffs n) = _
    rw [zero_nsmul]
    rfl
  succ_nsmul := by
    intro k p
    apply Poly.ext_coeffs
    ext n
    show (k + 1) • (p.coeffs n) = _
    rw [succ_nsmul]
    rfl

instance [Add P] [Neg P] [Sub P] [SMul ℕ P] [SMul ℤ P] [IsNegZeroClass P] [IsSubNegMonoid P] : IsSubNegMonoid P[X] where
  sub_eq_add_neg p q := by
    apply Poly.ext_coeffs
    ext n
    show p.coeffs n - q.coeffs n = p.coeffs n + -q.coeffs n
    rw [sub_eq_add_neg]
  zsmul_ofNat k p := by
    apply Poly.ext_coeffs
    ext n
    show (k: ℤ) • p.coeffs n = _
    apply zsmul_ofNat
  zsmul_negSucc k p := by
    apply Poly.ext_coeffs
    ext n
    show (Int.negSucc k) • p.coeffs n = _
    apply zsmul_negSucc

instance [Add P] [Neg P] [Sub P] [SMul ℕ P] [SMul ℤ P] [IsAddGroup P] : IsAddGroup P[X] where
  neg_add_cancel a := by
    apply Poly.ext_coeffs
    ext n
    show -a.coeffs n + _ = 0
    rw [neg_add_cancel]

instance [Neg P] [IsNegZeroClass P] [IsInvolutiveNeg P] : IsInvolutiveNeg P[X] where
  neg_neg a := by
    apply ext_coeffs
    ext n
    show - -a.coeffs n = _
    rw [neg_neg]

instance [Add P] [Neg P] [Sub P] [SMul ℕ P] [SMul ℤ P] [IsNegZeroClass P] [IsSubtractionMonoid P] : IsSubtractionMonoid P[X] where
  neg_add_rev := by
    intro a b
    apply ext_coeffs
    ext n
    show -(a.coeffs n + b.coeffs n) = -b.coeffs n + -a.coeffs n
    rw [neg_add_rev]
  neg_eq_of_add_left := by
    intro a b eq
    apply ext_coeffs
    ext n
    show -a.coeffs n = b.coeffs n
    apply neg_eq_of_add_left
    show (a + b).coeffs n = 0
    rw [eq]
    rfl

instance [Add P] [IsAddZeroClass P] [IsAddCommMagma P] : IsAddCommMagma P[X] where
  add_comm := by
    intro p q
    apply Poly.ext_coeffs
    ext n
    show p.coeffs n + q.coeffs n = q.coeffs n + p.coeffs n
    rw [add_comm]

variable [Add P] [Mul P] [IsAddZeroClass P] [IsMulZeroClass P]

instance [IsMulZeroClass P] : IsMulZeroClass P[X] where
  zero_mul a := by
    apply Poly.ext_coeffs
    ext n
    show Fin.sum _ = 0
    apply Fin.sum_eq_zero_of_each_eq_zero
    intro x
    erw [zero_mul]
  mul_zero a := by
    apply Poly.ext_coeffs
    ext n
    show Fin.sum _ = 0
    apply Fin.sum_eq_zero_of_each_eq_zero
    intro x
    erw [mul_zero]

private
def eq_div_mul_add (p: P[X]) :
  p = p.div_var.mul_var + const (p.coeffs 0) := by
  apply Poly.ext_coeffs
  ext n
  cases n with
  | zero =>
    show _ = _ + _
    dsimp
    erw [zero_add]
    rfl
  | succ n =>
    show _ = _ + _
    erw [add_zero]
    rfl

def zero_eq_const : (0: P[X]) = const 0 := by
  apply ext_coeffs
  ext n
  cases n <;> rfl

def const_mul_const (a b: P) : const a * const b = const (a * b) := by
  apply ext_coeffs
  ext n
  cases n
  show Fin.sum _ = a * b
  rw [Fin.sum, Fin.sum_eq_zero_of_each_eq_zero, add_zero]; rfl
  intro x
  exact x.elim0
  apply Fin.sum_eq_zero_of_each_eq_zero
  intro x
  match x with
  | ⟨0, _⟩ =>
    unfold const
    dsimp
    rw [mul_zero]
  | ⟨x + 1, _⟩ =>
    unfold const
    dsimp
    rw [zero_mul]

def mul_var_zero : Poly.mul_var (0: P[X]) = 0 := by
  apply ext_coeffs
  ext i
  cases i <;> rfl

def coeffs_congr {p q: P[X]} (h: p = q) : p.coeffs = q.coeffs := by rw [h]

@[induction_eliminator]
def induction {motive: P[X] -> Prop}
  (const: ∀a, motive (const a))
  (mul_add: ∀a: P, ∀p: P[X], p ≠ 0 -> motive p -> motive (Poly.const a) -> motive (p.mul_var + Poly.const a)): ∀p, motive p := by
  intro p
  cases p with
  | mk p has_deg =>
  induction has_deg using Quot.ind with | mk has_deg =>
  obtain ⟨degree, spec⟩ := has_deg
  induction degree generalizing p with
  | zero =>
    have p_eq_const : Poly.const (p 0) = ⟨p, Squash.mk ⟨0, spec⟩⟩ := by
      apply Poly.ext_coeffs
      ext n
      cases n
      rfl
      show 0 = _
      dsimp
      rw [spec]
      apply Nat.zero_lt_succ
    erw [←p_eq_const]
    apply const
  | succ degree ih =>
    by_cases h:(p ∘ Nat.succ)=(0: P[X]).coeffs
    · rw [eq_div_mul_add ⟨_, _⟩]
      have p_eq_const : Poly.div_var { coeffs := p, has_degree := Quot.mk (fun x x => True) ⟨degree + 1, spec⟩ } = { coeffs := coeffs 0, has_degree := Quot.mk (fun x x => True) ⟨0, ?_⟩ } := by
        apply Poly.ext_coeffs
        ext n
        simp
        simp [div_var]
        rw [←h]
        rfl
      intro _ _; rfl
      rw [p_eq_const]
      show motive (Poly.mul_var 0 + _)
      rw [mul_var_zero, zero_add]
      simp
      apply const
    · rw [eq_div_mul_add ⟨_, _⟩]
      apply mul_add
      · intro g
        have := coeffs_congr g
        simp [div_var] at this
        contradiction
      apply ih
      apply const

variable [IsLeftDistrib P] [IsRightDistrib P] [IsAddSemigroup P] [IsAddCommMagma P]

instance : IsLeftDistrib P[X] where
  left_distrib := by
    intro k a b
    apply Poly.ext_coeffs
    ext n
    show Fin.sum (fun _ => _ * (_ + _)) = Fin.sum _ + Fin.sum _
    rw [Fin.sum_add_sum]
    congr
    funext m
    rw [mul_add]

instance : IsRightDistrib P[X] where
  right_distrib := by
    intro k a b
    apply Poly.ext_coeffs
    ext n
    show Fin.sum (fun _ => (_ + _) * _) = Fin.sum _ + Fin.sum _
    rw [Fin.sum_add_sum]
    congr
    funext m
    rw [add_mul]

instance [IsCommMagma P] : IsCommMagma P[X] where
  mul_comm := by
    intro p q
    induction p with
    | const =>
      apply ext_coeffs
      ext n
      show Fin.sum _ = Fin.sum _
      rw [Fin.sum_rev]
      congr
      ext x
      unfold const
      dsimp
      rw [Nat.succ_sub_succ, Nat.sub_sub_eq_min, Nat.min_eq_right, mul_comm]
      apply Nat.le_of_lt_succ
      exact x.isLt
    | mul_add a p _ ih =>
      rw [add_mul, mul_add, mul_var_mul, mul_mul_var, ih]
      congr 1

instance [IsSemigroup P] : IsSemigroup P[X] where
  mul_assoc := by
    intro a b c
    induction a with
    | const a =>
      induction b with
      | const b =>
        induction c with
        | const c => simp [const_mul_const, mul_assoc]
        | mul_add k c ih =>
          simp [mul_add, add_mul, mul_var_mul, mul_mul_var]
          congr 2
      | mul_add k b ih =>
        simp [mul_add, add_mul, mul_var_mul, mul_mul_var]
        congr 2
    | mul_add k a ih =>
      simp [add_mul, mul_var_mul]
      congr

instance [IsMulOneClass P] : IsMulOneClass P[X] where
  mul_one a := by
    show a * const 1 = a
    apply ext_coeffs
    ext n
    cases n
    show Fin.sum _ = _
    rw [Fin.sum]
    show a.coeffs 0 * 1 + _ = _
    rw [mul_one, Fin.sum_eq_zero_of_each_eq_zero, add_zero]
    intro x
    exact x.elim0
    show a.coeffs 0 * 0 + _ = _
    rw [mul_zero, zero_add, Fin.sum_pop]
    dsimp
    erw [Nat.sub_self, mul_one, Fin.sum_eq_zero_of_each_eq_zero, zero_add]
    intro x
    rw [Nat.succ_sub_succ]
    rename_i n
    match n, x with
    | n + 1, ⟨x, _⟩ =>
    dsimp
    erw [Nat.succ_sub, mul_zero]
    apply Nat.le_of_lt_succ
    assumption
  one_mul a := by
    show const 1 * a = a
    apply ext_coeffs
    ext n
    cases n
    show Fin.sum _ = _
    rw [Fin.sum]
    show 1 * a.coeffs 0 + _ = _
    rw [one_mul, Fin.sum_eq_zero_of_each_eq_zero, add_zero]
    intro x
    exact x.elim0
    show Fin.sum _ = _
    erw [Fin.sum, one_mul, Fin.sum_eq_zero_of_each_eq_zero, add_zero]
    rfl
    intro x
    dsimp
    erw [zero_mul]

end

instance [AddGroupOps P] [IsAddGroup P] : IsAddGroup P[X] where
  neg_add_cancel a := by
    apply ext_coeffs
    ext i
    apply neg_add_cancel

instance [AddMonoidWithOneOps P] [IsAddMonoidWithOne P] : IsAddMonoidWithOne P[X] where
  natCast_zero := by
    apply ext_coeffs
    ext i; cases i
    apply natCast_zero
    rfl
  natCast_succ n := by
    apply ext_coeffs
    ext i
    cases i
    apply natCast_succ
    symm; apply zero_add
  ofNat_eq_natCast n := by
    apply ext_coeffs
    ext i
    cases i
    apply ofNat_eq_natCast
    rfl

instance [AddGroupWithOneOps P] [IsAddGroupWithOne P] : IsAddGroupWithOne P[X] := {
  instIsAddMonoidWithOne, instIsAddGroup with
  intCast_ofNat n := by
    apply ext_coeffs
    ext i; cases i
    apply intCast_ofNat
    rfl
  intCast_negSucc n := by
    apply ext_coeffs
    ext i; cases i
    apply intCast_negSucc
    symm; apply neg_zero
}
instance [SemiringOps P] [IsSemiring P] : IsSemiring P[X] where
instance [RingOps P] [IsRing P] : RingOps P[X] := RingOps.mk
instance [RingOps P] [IsRing P] : IsRing P[X] := inferInstance

instance [SemiringOps P] [IsSemiring P] : AlgebraMap P P[X] where
  toFun := const
  resp_zero := by
    apply ext_coeffs
    ext i; cases i <;> rfl
  resp_one := by
    apply ext_coeffs
    ext i; cases i <;> rfl
  resp_add {_ _} := by
    apply ext_coeffs
    ext i
    cases i
    rfl
    symm; apply zero_add
  resp_mul {x y} := by
    symm; apply const_mul_const

def smul_const [Zero P] [Mul P] [IsMulZeroClass P] (r p: P) : r • const p = const (r * p) := by
  apply ext_coeffs
  ext i; cases i
  rfl
  apply mul_zero

def smul_mul_var [Zero P] [Mul P] [IsMulZeroClass P] (r: P) (p: P[X]) : r • p.mul_var = (r • p).mul_var := by
  apply ext_coeffs
  ext i; cases i
  apply mul_zero
  rfl

def smul_add' [SemiringOps P] [IsSemiring P] (r: P) (p q: P[X]) : r • (p + q) = r • p + r • q := by
  apply ext_coeffs
  ext i
  apply mul_add

instance [SemiringOps P] [IsSemiring P] [IsCommMagma P] : IsAlgebra P P[X] where
  commutes _ _ := by rw [mul_comm]
  smul_def r p := by
    induction p with
    | const =>
      rw [smul_const, ←const_mul_const]
      rfl
    | mul_add p ps ps_ne_zero ih₀ ih₁ =>
      simp [smul_add', smul_mul_var, smul_const, ih₀, ih₁,
        mul_add, ←mul_mul_var]

instance [Zero P] [Subsingleton P] : Subsingleton P[X] where
  allEq := by
    intro a b
    apply ext_coeffs
    apply Subsingleton.allEq

instance [Zero P] [h: IsNontrivial P] : IsNontrivial P[X] where
  exists_ne := by
    have ⟨a, b, ne⟩ := h.exists_ne
    refine ⟨const a, const b, ?_⟩
    intro h
    have : (const a).coeffs 0 = (const b).coeffs 0 := by rw [h]
    contradiction

def constHom [SemiringOps P] [IsSemiring P] : P →+* P[X] := algebraMap

def X [Zero P] [One P] : P[X] := Poly.ofCoeffs [0, 1]

def mul_X [SemiringOps P] [IsSemiring P] (p: P[X]) : p * X = p.mul_var := by
  apply ext_coeffs
  ext i
  match i with
  | 0 =>
    apply Fin.sum_eq_zero_of_each_eq_zero
    intro x
    match x with
    | 0 => erw [mul_zero]
  | 1 =>
    show Fin.sum _ = p.coeffs 0
    rw [Fin.sum, Fin.sum, Fin.sum, add_zero]
    erw [mul_one]
    simp
    erw [mul_zero, add_zero]
  | i + 2 =>
    show Fin.sum _ = p.coeffs (i + 1)
    rw [Fin.sum_succ', Fin.sum_succ', Fin.sum_eq_zero_of_each_eq_zero, zero_add]
    simp [Fin.last]
    erw [mul_zero, Nat.add_sub_cancel_left, mul_one, add_zero]
    intro ⟨x, xLt⟩
    simp
    rw [Nat.lt_succ] at xLt
    rcases lt_or_eq_of_le xLt with xLt | rfl
    simp [X, ofCoeffs]
    rw [List.getElem?_eq_none, Option.getD, mul_zero]
    simp; omega
    erw [Nat.add_sub_cancel_left, mul_zero]


end Poly
