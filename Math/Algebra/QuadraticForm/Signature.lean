import Math.Algebra.Impls.Pi
import Math.Algebra.QuadraticForm
import Math.Data.Fintype.Algebra
import Math.Data.Fintype.Fin
import Math.Data.Fintype.Prod

@[local simp]
private def pi_add [Add R] : ∀{ι} (a b: ι -> R) (x: ι), (a + b) x = a x + b x :=
   fun _ _ _ => rfl

def QuadraticForm.ofNonnegSignature [SemiringOps R] [IsSemiring R] [IsCommMagma R] (z p: ℕ) : QuadraticForm R (Fin (z + p) -> R) where
  toFun v := Fintype.sum (fun x: Fin p =>
    let x := x.natAdd z
    v x * v x)
  toFun_smul a v := by
    dsimp
    rw [smul_eq_mul, Fintype.mul_sum]
    congr; ext i
    simp [SMul.smul]
    ac_rfl
  exists_companion' := by
    refine ⟨?_, ?_⟩
    apply BilinMap.mk (fun a b => Fintype.sum (fun x: Fin p => 2 * a (x.natAdd z) * b (x.natAdd z)))
    · intro a b k
      rw [Fintype.sum_add]
      congr; ext i
      rw [←add_mul, ←mul_add]
      rfl
    · intro k a b
      rw [Fintype.sum_add]
      congr; ext i
      rw [←mul_add]
      rfl
    · intro r a k
      simp [Fintype.mul_sum]
      congr; ext i
      rw [←mul_assoc, mul_left_comm]
      rfl
    · intro r a k
      simp [Fintype.mul_sum]
      congr; ext i
      rw [mul_left_comm]
      rfl
    · intro a b
      simp [DFunLike.coe, BilinMap.mk]
      rw [Fintype.sum_add, Fintype.sum_add]
      congr; ext i
      simp [add_mul, mul_add, two_mul]
      ac_nf

def QuadraticForm.ofSignature [RingOps R] [IsRing R] [IsCommMagma R] (z p n: ℕ) : QuadraticForm R (Fin (z + p + n) -> R) where
  toFun v := Fintype.sum (fun x: Fin p =>
    let x := (x.natAdd z).castAdd n
    v x * v x) + Fintype.sum (fun x: Fin n =>
    let x := x.natAdd (z + p)
    (-(v x * v x)))
  toFun_smul a v := by
    dsimp
    rw [smul_eq_mul, mul_add, Fintype.mul_sum, Fintype.mul_sum]
    congr
    ext i
    simp [SMul.smul]
    ac_rfl
    ext i
    simp [SMul.smul]
    rw [←neg_mul_right]
    ac_rfl
  exists_companion' := by
    refine ⟨?_, ?_⟩
    apply BilinMap.mk (fun a b => Fintype.sum (fun x: Fin p =>
      let x := (x.natAdd z).castAdd n
      2 * a x * b x) + Fintype.sum (fun x: Fin n =>
      let x := x.natAdd (z + p)
      (-(2 * a x * b x))))
    · intro a b k
      simp
      ac_nf
      repeat rw [←add_assoc (α:= R), Fintype.sum_add]
      rw [Fintype.sum_add]
      congr
      · ext i
        simp [mul_add, two_mul, mul_two]
        ac_nf
      · ext i
        simp [mul_add, two_mul, mul_two, ←neg_add_rev]
        ac_nf
    · intro k a b
      simp
      ac_nf
      repeat rw [←add_assoc (α:= R), Fintype.sum_add]
      rw [Fintype.sum_add]
      congr
      · ext i
        simp [mul_add, two_mul, mul_two]
      · ext i
        simp [mul_add, two_mul, mul_two, ←neg_add_rev]
        ac_nf
    · intro r a k
      rw [smul_add, smul_eq_mul, smul_eq_mul]
      rw [Fintype.mul_sum, Fintype.mul_sum]
      congr
      · ext i
        simp
        rw [←mul_assoc, mul_left_comm]
        rfl
      · ext i
        simp
        rw [←neg_mul_right, ←mul_assoc, mul_left_comm]
        rfl
    · intro r a k
      rw [smul_add, smul_eq_mul, smul_eq_mul]
      rw [Fintype.mul_sum, Fintype.mul_sum]
      congr
      · ext i
        simp
        rw [mul_left_comm]
        rfl
      · ext i
        simp
        rw [←neg_mul_right, mul_left_comm]
        rfl
    · intro a b
      simp [BilinMap.mk, DFunLike.coe]
      ac_nf
      repeat rw [←add_assoc (α:= R), Fintype.sum_add]
      rw [add_assoc (α:= R), Fintype.sum_add]
      congr
      · ext i
        simp [mul_two, add_mul, mul_add]
        ac_rfl
      · ext i
        simp [mul_two, add_mul, mul_add, ←neg_add_rev]
        ac_rfl
