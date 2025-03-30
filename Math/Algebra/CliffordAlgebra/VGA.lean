import Math.Algebra.QuadraticForm.Signature
import Math.Algebra.CliffordAlgebra.Defs
import Math.Data.Real.Basic
import Math.Data.Fin.Sum

namespace VGA

abbrev Vector (n: ℕ) := Fin n -> ℝ

def QF (n: ℕ) : QuadraticForm ℝ (Vector n) := (QuadraticForm.ofSignature' 0 n 0 n (Nat.zero_add _).symm)

end VGA

def VGA (n: ℕ) := CliffordAlgebra (R := ℝ) (VGA.QF n)

namespace VGA

instance : RingOps (VGA n) := inferInstanceAs (RingOps (CliffordAlgebra _))
instance instRing : IsRing (VGA n) := inferInstanceAs (IsRing (CliffordAlgebra _))
instance : IsSemiring (VGA n) := instRing.toIsSemiring
instance : SMul ℝ (VGA n) := inferInstanceAs (SMul ℝ (CliffordAlgebra _))
instance : IsModule ℝ (VGA n) := inferInstanceAs (IsModule ℝ (CliffordAlgebra _))
instance : AlgebraMap ℝ (VGA n) := inferInstanceAs (AlgebraMap ℝ (CliffordAlgebra _))
instance : IsAlgebra ℝ (VGA n) := inferInstanceAs (IsAlgebra ℝ (CliffordAlgebra _))

def ι : (Vector n) →ₗ[ℝ] VGA n := CliffordAlgebra.ι (R := ℝ) (QF n)
def ι_sq (v: Vector n) : ι v * ι v = algebraMap (QF n v) := CliffordAlgebra.ι_sq_scalar _ _
def ι_mul_add_comm_mul (v w: Vector n) : ι v * ι w + ι w * ι v = algebraMap ((QF n).polar v w) := CliffordAlgebra.ι_mul_add_comm_mul _ _ _

instance : IsZeroHom ((Vector n) →ₗ[ℝ] VGA n) (Vector n) (VGA n) where
  map_zero f := by rw [←smul_zero (0: ℝ), map_smul, zero_smul]

set_option linter.unusedVariables false in
@[induction_eliminator]
def induction {C : VGA n → Prop} :
  ∀(algebraMap: ∀r: ℝ, C (algebraMap r)) (ι: ∀ x, C (ι x))
   (mul: ∀ a b, C a → C b → C (a * b)) (add: ∀ a b, C a → C b → C (a + b))
   (a : VGA n), C a := CliffordAlgebra.induction (C := C)

def basis_vector (i: Fin n) : Vector n := fun j => if i = j then 1 else 0

def basis_mvector (i: Fin (2 ^ n)) : VGA n :=
  Fin.prod fun j: Fin n =>
    if i &&& (1 <<< j.val) == 0 then
      1
    else
      ι (basis_vector j)

-- def basis (v: VGA n) : ∃c: Fin (2 ^ n) -> ℝ, v = Fin.sum fun i: Fin (2 ^ n) => c i • basis_mvector i := by
--   induction v with
--   | algebraMap r =>
--     refine ⟨fun
--       | ⟨0, _⟩ => r
--       | ⟨_ + 1, _⟩ => 0, ?_⟩
--     rw [
--       Fin.sum_cast (m := (2 ^ n - 1 + 1)),
--       Fin.sum_succ', Fin.sum_eq_zero]
--     simp
--     unfold OfNat.ofNat Fin.instOfNat instOfNatNat
--       Fin.ofNat'
--     simp
--     rw [smul_def]
--     rw [show basis_mvector ⟨0, _⟩ = 1 from ?_, mul_one]
--     unfold basis_mvector
--     rw [Fin.prod_eq_one]
--     intro x
--     rw [if_pos]
--     simp
--     intro x
--     simp
--     rw [Fin.cast]
--     simp [zero_smul]
--     rw [Nat.sub_add_cancel]
--     exact Nat.one_le_two_pow
--   | ι v =>
--     refine ⟨fun i =>
--       if h:∃m < n, i.val == (1 <<< m) then
--         v ⟨Nat.findP h, (Nat.findP_spec h).left⟩
--       else
--         0, ?_⟩
--     induction n with
--     | zero =>
--       rw [Fin.sum_succ, Fin.sum_zero]
--       dsimp
--       rw [zero_add, zero_smul]
--       rw [←zero_smul (R := ℝ) (ι v), ←map_smul]
--       congr
--       ext i; exact i.elim0
--     | succ n ih =>
--       simp at *
--       rw [Fin.sum_cast (m := 2 ^ n + (2 ^ n - 1) + 1) (by
--         rw [Nat.add_assoc, Nat.sub_add_cancel]
--         omega
--         exact Nat.one_le_two_pow),
--         Fin.sum_succ, Fin.sum_limit (m := 2 ^ n) (by
--           exact Nat.le_add_right (2 ^ n) (2 ^ n - 1))]
--       simp only [Function.comp_def, Fin.cast, Fin.castLE, Fin.castSucc, Fin.castAdd]
--       sorry
--       sorry
--   | add => sorry
--   | mul => sorry

-- def basis (v: VGA n) : ∃c: Fin (2 ^ n) -> ℝ, v = Fin.sum fun i: Fin (2 ^ n) => c i • basis_mvector i := by
--   induction v with
--   | algebraMap v =>
--     refine ⟨fun
--       | ⟨0, _⟩ => v
--       | ⟨_ + 1, _⟩ => 0, ?_⟩
--     rw [
--       Fin.sum_cast (m := (2 ^ n - 1 + 1)),
--       Fin.sum_succ', Fin.sum_eq_zero]
--     simp
--     unfold OfNat.ofNat Fin.instOfNat instOfNatNat
--       Fin.ofNat'
--     simp
--     rw [smul_def]
--     rw [show basis_mvector ⟨0, _⟩ = 1 from ?_, mul_one]
--     unfold basis_mvector
--     rw [Fin.prod_eq_one]
--     intro x
--     rw [if_pos]
--     simp
--     intro x
--     simp
--     rw [Fin.cast]
--     simp [zero_smul]
--     rw [Nat.sub_add_cancel]
--     exact Nat.one_le_two_pow
--   | ι v =>
--     refine ⟨fun i =>
--       if h:i.val = 0 then
--         0
--       else if g: i <= n then
--         v ⟨i.val - 1, by
--           refine Nat.sub_one_lt_of_le ?_ g
--           refine Nat.zero_lt_of_ne_zero ?_
--           assumption⟩
--       else
--         0, ?_⟩
--     rw [Fin.sum_limit (n + 1) (by sorry)]
--     · sorry
--       -- induction n with
--       -- | zero =>
--       --   rw [Fin.sum_succ, Fin.sum_zero, zero_add]
--       --   simp
--       --   rw [zero_smul, show v = ((0: ℝ) • 0) from ?_, map_smul, zero_smul]
--       --   rw [zero_smul]
--       --   ext i
--       --   exact i.elim0
--       -- | succ n ih =>
--       --   rw [Fin.sum_succ]
--       --   sorry
--     · intro x hx
--       simp
--       split
--       rw [zero_smul]
--       split
--       rename_i h
--       have := not_lt_of_le (le_trans hx h) (Nat.lt_succ_self _)
--       contradiction
--       rw [zero_smul]
--   | add a b ha hb =>
--     obtain ⟨a, rfl⟩ := ha
--     obtain ⟨b, rfl⟩ := hb
--     refine ⟨fun i => a i + b i, ?_⟩
--     simp [map_add, add_smul]
--     ac_rfl
--   | mul a b ha hb =>
--     sorry
--     -- obtain ⟨a, rfl⟩ := ha
--     -- obtain ⟨b, rfl⟩ := hb
--     -- refine ⟨?_, ?_⟩
--     -- exact fun
--     --   | 0 => algebraMap (a 0 * b 0)
--     --   | 1 => sorry
--     --   | 2 => sorry
--     --   | 3 => sorry
--     --   | 4 => sorry
--     --   | 5 => sorry
--     --   | 6 => sorry
--     --   | 7 => sorry
--     -- simp only [add_mul, mul_add, algebraMap_id, ←map_mul]
--     -- simp only [←commutes (R := ℝ) (A := VGA 3), ←smul_def, ←mul_smul,
--     --   smul_mul]
--     -- simp only [ι_sq, i_sq, j_sq, k_sq, smul_one]

--     -- repeat rw [add_assoc]
--     -- congr 1

namespace VGA3

def dot (v w: Vector 3) : ℝ := v 0 * w 0 + v 1 * w 1 + v 2 * w 2

def i : Vector 3 := basis_vector 0
def j : Vector 3 := basis_vector 1
def k : Vector 3 := basis_vector 2

def ι_eq_lincomb (v: Vector 3) : ι v = v 0 • ι i + v 1 • ι j + v 2 • ι k := by
  simp only [←map_smul, ←map_add]
  congr
  unfold i j k
  ext i
  simp
  unfold basis_vector
  match i with
  | 0 =>
    rw [if_pos, if_neg, if_neg]
    simp
    all_goals decide
  | 1 =>
    rw [if_neg, if_pos, if_neg]
    simp
    all_goals decide
  | 2 =>
    rw [if_neg, if_neg, if_pos]
    simp
    all_goals decide

example : ι i * ι j = -ι j * ι i := by
  rw [←neg_mul_left]
  refine neg_eq_of_add_right ?_
  rw [ι_mul_add_comm_mul]
  rfl

@[simp] def i_sq : algebraMap (QF 3 i) = (1: VGA 3) := rfl
@[simp] def j_sq : algebraMap (QF 3 j) = (1: VGA 3) := rfl
@[simp] def k_sq : algebraMap (QF 3 k) = (1: VGA 3) := rfl

@[simp]
def anticomm_ij : ι j * ι i = -(ι i * ι j) := by
  symm
  refine neg_eq_of_add_left ?_
  rw [ι_mul_add_comm_mul]
  rfl
@[simp]
def anticomm_ik : ι k * ι i = -(ι i * ι k) := by
  symm
  refine neg_eq_of_add_left ?_
  rw [ι_mul_add_comm_mul]
  rfl
@[simp]
def anticomm_jk : ι k * ι j = -(ι j * ι k) := by
  symm
  refine neg_eq_of_add_left ?_
  rw [ι_mul_add_comm_mul]
  rfl

def anticomm' (v w: Vector 3) : ι v * ι w = -ι w * ι v + 2 * algebraMap (dot v w) := by
  rw [←neg_mul_left]
  apply add_left_cancel (k := ι w * ι v)
  rw [←add_assoc, add_neg_cancel, zero_add]
  rw [ι_eq_lincomb v, ι_eq_lincomb w]
  simp [smul_add, add_mul, mul_add, i, j, k,
    one_smul, zero_smul, smul_mul,
    ι_sq, smul_one]
  ac_nf
  repeat rw [←add_assoc, smul_neg, neg_add_cancel, zero_add]
  repeat rw [←map_add]
  sorry
  -- rw [←add_assoc, ←two_mul, ←add_assoc (v 1 * _), ←two_mul, ←two_mul]
  -- rw [←mul_add, ←mul_add, ←add_assoc]
  -- rw [map_mul]
  -- rfl

def ijk_sq : (ι i * ι j * ι k) ^ 2 = -1 := by
  rw [npow_two, ←mul_assoc, ←mul_assoc]
  repeat rw [mul_assoc (ι i)]
  repeat rw [mul_assoc (ι j)]
  rw [anticomm_ik]; simp only [←neg_mul_left, ←neg_mul_right]
  rw [mul_assoc (ι i), anticomm_jk]; simp only [←neg_mul_left, ←neg_mul_right]
  rw [mul_assoc, mul_assoc, ι_sq,
    ←mul_assoc (ι j), anticomm_ij]; simp only [←neg_mul_left, ←neg_mul_right]
  rw [←mul_assoc, ←mul_assoc, ←mul_assoc, mul_assoc (_ * ι i),
    ι_sq, ι_sq]
  simp [neg_neg]

-- def basis (v: VGA 3) : ∃c: Fin 8 -> ℝ, v = algebraMap (A := VGA 3) (c 0)
--   + c 1 • ι i + c 2 • ι j + c 3 • ι k
--   + c 4 • (ι i * ι j) + c 5 • (ι i * ι k) + c 6 • (ι j * ι k)
--   + c 7 • (ι i * ι j * ι k) := by
--   induction v with
--   | algebraMap v =>
--     refine ⟨fun
--       | 0 => v
--       | ⟨_ + 1, _⟩ => 0, ?_⟩
--     simp [zero_smul]
--   | ι v =>
--     refine ⟨fun
--       | 1 => v 0
--       | 2 => v 1
--       | 3 => v 2
--       | _ => 0, ?_⟩
--     simp [zero_smul, map_zero]
--     rw [ι_eq_lincomb]
--   | add a b ha hb =>
--     obtain ⟨a, rfl⟩ := ha
--     obtain ⟨b, rfl⟩ := hb
--     refine ⟨fun i => a i + b i, ?_⟩
--     simp [map_add, add_smul]
--     ac_rfl
--   | mul a b ha hb =>
--     obtain ⟨a, rfl⟩ := ha
--     obtain ⟨b, rfl⟩ := hb
--     refine ⟨?_, ?_⟩
--     exact fun
--       | 0 => algebraMap (a 0 * b 0)
--       | 1 => sorry
--       | 2 => sorry
--       | 3 => sorry
--       | 4 => sorry
--       | 5 => sorry
--       | 6 => sorry
--       | 7 => sorry
--     simp only [add_mul, mul_add, algebraMap_id, ←map_mul]
--     simp only [←commutes (R := ℝ) (A := VGA 3), ←smul_def, ←mul_smul,
--       smul_mul]
--     simp only [ι_sq, i_sq, j_sq, k_sq, smul_one]

--     -- repeat rw [add_assoc]
--     -- congr 1




--     congr
--     repeat sorry

end VGA3

end VGA
