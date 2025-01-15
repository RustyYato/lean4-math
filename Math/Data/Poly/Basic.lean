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

variable [One α] [Add α] [Mul α] [Pow α ℕ] [IsAddZeroClass α] [IsMulZeroClass α] [IsMonoid α]

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

def Poly.ext_coeffs (a b: Poly α) : a.coeffs = b.coeffs -> a = b := by
  intro h
  cases a;cases b; congr
  apply Subsingleton.helim
  dsimp at h
  rw [h]

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
  nsmul_zero p := by
    apply Poly.ext_coeffs
    ext n
    show 0 • (p.coeffs n) = _
    rw [zero_nsmul]
    rfl
  nsmul_succ := by
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

instance [Add α] [IsAddZeroClass α] [IsAddCommMagma α] : IsAddCommMagma (Poly α) where
  add_comm := by
    intro p q
    apply Poly.ext_coeffs
    ext n
    show p.coeffs n + q.coeffs n = q.coeffs n + p.coeffs n
    rw [add_comm]

end Poly
