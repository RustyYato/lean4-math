import Math.Function.Basic
import Math.Data.Like.Func
import Math.Data.StdNat.Find
import Math.Relation.Basic
import Math.Algebra.Ring
import Math.Data.Fin.Basic

def Poly.DegreeLe [Zero α] (f: Nat -> α) (bound: Nat) :=
  ∀n > bound, f n = 0

structure Poly (α: Type*) [Zero α] where
  coeffs: Nat -> α
  has_degree: Squash (Σ'bound: Nat, Poly.DegreeLe coeffs bound)

namespace Poly

variable [Zero α]

instance (priority := 100) [OfNat α n] : OfNat (Poly α) n where
  ofNat := {
    coeffs
    | 0 => OfNat.ofNat n
    | _ + 1 => 0
    has_degree := Squash.mk ⟨0, fun x _ => match x with | _ + 1 => rfl⟩
  }

instance [NatCast α] : NatCast (Poly α) where
  natCast n := {
    coeffs
    | 0 => (n: α)
    | _ + 1 => 0
    has_degree := Squash.mk ⟨0, fun x _ => match x with | _ + 1 => rfl⟩
  }

instance [IntCast α] : IntCast (Poly α) where
  intCast n := {
    coeffs
    | 0 => (n: α)
    | _ + 1 => 0
    has_degree := Squash.mk ⟨0, fun x _ => match x with | _ + 1 => rfl⟩
  }

instance [One α] : One (Poly α) := ⟨1⟩

instance : Zero (Poly α) where
  zero := {
    coeffs _ := 0
    has_degree := Squash.mk ⟨0, fun _ _ => rfl⟩
  }

section degree

variable [BEq α] [LawfulBEq α]

private
def findDegree (f: Nat -> α) : (Σ'm: Nat, Poly.DegreeLe f m) -> Σ'm: Nat, Poly.DegreeLe f m ∧ ∀x, Poly.DegreeLe f x -> m ≤ x
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

def degree (p: Poly α) : Nat := by
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

def degree.DegreeLe (p: Poly α) : Poly.DegreeLe p.coeffs p.degree := by
  cases p with
  | mk f h =>
  induction h using Quot.ind with
  | mk h =>
  dsimp
  exact (Poly.findDegree f h).snd.left

def degree_is_minimal (p: Poly α) : ∀x, Poly.DegreeLe p.coeffs x -> p.degree ≤ x := by
  cases p with
  | mk f h =>
  induction h using Quot.ind with
  | mk h =>
  dsimp
  exact (Poly.findDegree f h).snd.right

end degree

def ofCoeffs (coeffs: List α) : Poly α where
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
def mul_var (p: Poly α): Poly α where
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
def div_var (p: Poly α): Poly α where
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

def const (k: α) : Poly α where
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

instance [Add α] [IsAddZeroClass α] : Add (Poly α) where
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

instance [Add α] [Mul α] [IsAddZeroClass α] [IsMulZeroClass α] : Mul (Poly α) where
  mul a b := Poly.mk (fun n => Fin.sum (n := n + 1) fun x => a.coeffs x.val * b.coeffs (n - x.val)) <| by
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
    dsimp
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

instance [Neg α] [IsNegZeroClass α] : Neg (Poly α) where
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

instance [Add α] [SMul ℕ α] [IsAddMonoid α] : SMul ℕ (Poly α) where
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

instance [Add α] [Mul α] [IsMulZeroClass α] : SMul α (Poly α) where
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

instance [Add α] [Neg α] [Sub α] [SMul ℕ α] [SMul ℤ α] [IsNegZeroClass α] [IsSubNegMonoid α] : SMul ℤ (Poly α) where
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

instance [Add α] [Neg α] [Sub α] [SMul ℕ α] [SMul ℤ α] [IsNegZeroClass α] [IsSubNegMonoid α] : Sub (Poly α) where
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

instance [Neg α] [IsNegZeroClass α] : Neg (Poly α) where
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

variable [One α] [Add α] [Mul α] [Pow α ℕ] [IsAddZeroClass α] [IsMulZeroClass α] [IsMonoid α]

instance : Pow (Poly α) ℕ := ⟨flip npowRec⟩

def eval (p: Poly α) (x: α) : α := by
  apply Quot.liftOn p.has_degree _ _
  intro ⟨bound, spec⟩
  refine Fin.sum (n := bound+1) ?_
  intro n
  exact p.coeffs n.val * x ^ n.val
  intro ⟨a, bound_a⟩ ⟨b, bound_b⟩ _
  dsimp
  cases p with
  | mk  p h =>
  dsimp
  dsimp at bound_a bound_b
  clear h
  apply Fin.sum_eq_sum_of_prefix
  intro; rfl
  intro n b_le_n
  rw [bound_b, zero_mul]
  apply Nat.lt_of_le_of_lt _ b_le_n
  apply Nat.le_refl
  intro n a_le_n
  rw [bound_a, zero_mul]
  apply Nat.lt_of_le_of_lt _ a_le_n
  apply Nat.le_refl

instance : CoeFun (Poly α) (fun _ => α -> α) := ⟨eval⟩

-- def ext_eval [IsAddLeftCancel α] (f g: Poly α) : (∀x, f x = g x) -> f = g := by
--   intro h
--   cases f with | mk f fbound =>
--   cases g with | mk g gbound =>
--   suffices f = g by
--     congr 1
--     apply Subsingleton.helim
--     rw [this]
--   ext x
--   induction fbound using Quot.ind with | mk fbound =>
--   induction gbound using Quot.ind with | mk gbound =>
--   obtain ⟨bound_f, bound_f_spec⟩ := fbound
--   obtain ⟨bound_g, bound_g_spec⟩ := gbound
--   unfold eval at h
--   dsimp [Quot.liftOn] at h
--   induction x using Nat.strongRecOn with
--   | ind x ih =>
--     refine if hfx:bound_f < x then ?_ else ?_
--     sorry
--     refine if hgx:bound_g < x then ?_ else ?_
--     sorry
--     cases x with
--     | zero =>
--       have := h 0
--       erw [Fin.sum, Fin.sum, npow_zero, mul_one, mul_one, Fin.sum_eq_zero_of_each_eq_zero,
--         Fin.sum_eq_zero_of_each_eq_zero, add_zero, add_zero] at this
--       exact this
--       intro x
--       dsimp
--       rw [npow_succ, mul_zero, mul_zero]
--       intro x
--       dsimp
--       rw [npow_succ, mul_zero, mul_zero]
--     | succ x =>
--       replace hfx := Nat.le_of_not_lt hfx
--       replace hgx := Nat.le_of_not_lt hgx
--       have h' := fun m => Fin.sum_strip_prefix x (by
--         apply Nat.le_trans _ (Nat.le_trans hfx _)
--         apply Nat.le_succ
--         apply Nat.le_succ) (by
--         apply Nat.le_trans _ (Nat.le_trans hgx _)
--         apply Nat.le_succ
--         apply Nat.le_succ) (by
--         intro ⟨n, n_lt_x⟩
--         dsimp
--         rw [ih]
--         apply Nat.lt_trans n_lt_x
--         apply Nat.lt_succ_self) (h m)
--       dsimp at h'
--       sorry

def ext_coeffs (a b: Poly α) : a.coeffs = b.coeffs -> a = b := by
  intro h
  cases a;cases b; congr
  apply Subsingleton.helim
  dsimp at h
  rw [h]

def mul_mul_var (p q: Poly α) : p * q.mul_var = (p * q).mul_var := by
  apply ext_coeffs
  ext n
  cases n
  show Fin.sum _ = 0
  apply Fin.sum_eq_zero_of_each_eq_zero
  intro x
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

def mul_var_mul (p q: Poly α) : p.mul_var * q = (p * q).mul_var := by
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

instance : IsAddZeroClass (Poly α) where
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

instance [IsAddSemigroup α] : IsAddSemigroup (Poly α) where
  add_assoc a b c := by
    apply Poly.ext_coeffs
    ext n
    show _ + _ + _ = _
    rw [add_assoc]
    rfl

instance [Neg α] [IsNegZeroClass α] : IsNegZeroClass (Poly α) where
  neg_zero := by
    apply Poly.ext_coeffs
    ext n
    show - 0 = _
    rw [neg_zero]
    rfl

instance [SMul ℕ α] [IsAddMonoid α] : IsAddMonoid (Poly α) where
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

instance [Add α] [Neg α] [Sub α] [SMul ℕ α] [SMul ℤ α] [IsNegZeroClass α] [IsSubNegMonoid α] : IsSubNegMonoid (Poly α) where
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

instance [Add α] [Neg α] [Sub α] [SMul ℕ α] [SMul ℤ α] [IsAddGroup α] : IsAddGroup (Poly α) where
  neg_add_cancel a := by
    apply Poly.ext_coeffs
    ext n
    show -a.coeffs n + _ = 0
    rw [neg_add_cancel]

instance [Neg α] [IsNegZeroClass α] [IsInvolutiveNeg α] : IsInvolutiveNeg (Poly α) where
  neg_neg a := by
    apply ext_coeffs
    ext n
    show - -a.coeffs n = _
    rw [neg_neg]

instance [Add α] [Neg α] [Sub α] [SMul ℕ α] [SMul ℤ α] [IsNegZeroClass α] [IsSubtractionMonoid α] : IsSubtractionMonoid (Poly α) where
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

instance [Add α] [IsAddZeroClass α] [IsAddCommMagma α] : IsAddCommMagma (Poly α) where
  add_comm := by
    intro p q
    apply Poly.ext_coeffs
    ext n
    show p.coeffs n + q.coeffs n = q.coeffs n + p.coeffs n
    rw [add_comm]

variable [Add α] [Mul α] [IsAddZeroClass α] [IsMulZeroClass α]

instance [IsMulZeroClass α] : IsMulZeroClass (Poly α) where
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
def eq_div_mul_add (p: Poly α) :
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

def zero_eq_const : (0: Poly α) = const 0 := by
  apply ext_coeffs
  ext n
  cases n <;> rfl

def const_mul_const (a b: α) : const a * const b = const (a * b) := by
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

@[induction_eliminator]
def induction {motive: Poly α -> Prop}
  (const: ∀a, motive (const a))
  (mul_add: ∀a: α, ∀p: Poly α, motive p -> motive (Poly.const a) -> motive (p.mul_var + Poly.const a)): ∀p, motive p := by
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
    rw [eq_div_mul_add ⟨_, _⟩]
    apply mul_add
    apply ih
    apply const

variable [IsLeftDistrib α] [IsRightDistrib α] [IsAddSemigroup α] [IsAddCommMagma α]

instance : IsLeftDistrib (Poly α) where
  left_distrib := by
    intro k a b
    apply Poly.ext_coeffs
    ext n
    show Fin.sum (fun _ => _ * (_ + _)) = Fin.sum _ + Fin.sum _
    rw [Fin.sum_add_sum]
    congr
    funext m
    rw [mul_add]

instance : IsRightDistrib (Poly α) where
  right_distrib := by
    intro k a b
    apply Poly.ext_coeffs
    ext n
    show Fin.sum (fun _ => (_ + _) * _) = Fin.sum _ + Fin.sum _
    rw [Fin.sum_add_sum]
    congr
    funext m
    rw [add_mul]

instance [IsCommMagma α] : IsCommMagma (Poly α) where
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
    | mul_add a p ih =>
      rw [add_mul, mul_add, mul_var_mul, mul_mul_var, ih]
      congr 1

instance [IsSemigroup α] : IsSemigroup (Poly α) where
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

instance [IsMulOneClass α] : IsMulOneClass (Poly α) where
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

instance [IsSemigroup α] [IsMulOneClass α] : IsMonoid (Poly α) where

instance [SMul ℕ α] [NatCast α] [∀n, OfNat α (n + 2)] [IsAddMonoidWithOne α] : IsAddMonoidWithOne (Poly α) where
  natCast_zero := by
    apply ext_coeffs
    ext x
    cases x
    apply natCast_zero
    rfl
  ofNat_zero := rfl
  ofNat_one := rfl
  ofNat_eq_natCast := by
    intro n
    apply ext_coeffs
    ext x
    cases x
    apply ofNat_eq_natCast
    rfl
  natCast_succ := by
    intro n
    apply ext_coeffs
    ext x
    cases x
    apply natCast_succ
    show _ = _ + 0
    rw [add_zero]
    rfl

instance [SMul ℕ α] [NatCast α] [∀n, OfNat α (n + 2)] [IsSemiring α] : IsSemiring (Poly α) where

instance [SMul ℕ α] [NatCast α] [∀n, OfNat α (n + 2)] [Sub α] [SMul ℤ α] [Neg α] [IntCast α] [IsAddGroupWithOne α] : IsAddGroupWithOne (Poly α) where
  natCast_zero := natCast_zero
  natCast_succ := natCast_succ
  ofNat_zero := rfl
  ofNat_one := rfl
  ofNat_eq_natCast := ofNat_eq_natCast
  intCast_ofNat n := by
    apply ext_coeffs
    ext x
    cases x
    apply intCast_ofNat
    rfl
  intCast_negSucc n := by
    apply ext_coeffs
    ext x
    cases x
    apply intCast_negSucc
    symm
    apply neg_zero

instance [SMul ℕ α] [NatCast α] [∀n, OfNat α (n + 2)] [Sub α] [SMul ℤ α] [Neg α] [IntCast α] [IsRing α] : IsRing (Poly α) where
  intCast_ofNat := intCast_ofNat
  intCast_negSucc := intCast_negSucc
  sub_eq_add_neg := by
    intro a b
    apply ext_coeffs
    ext x
    show a.coeffs x - b.coeffs x = _
    rw [sub_eq_add_neg]
    rfl
  neg_add_cancel := by
    intro a
    apply ext_coeffs
    ext x
    show -a.coeffs x + a.coeffs x = _
    rw [neg_add_cancel]
    rfl
  zsmul_ofNat := by
    intro n a
    apply ext_coeffs
    ext x
    apply zsmul_ofNat
  zsmul_negSucc := by
    intro n a
    apply ext_coeffs
    ext x
    apply zsmul_negSucc

end Poly
