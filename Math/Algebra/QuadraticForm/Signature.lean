import Math.Algebra.Impls.Pi
import Math.Algebra.QuadraticForm.Basic
import Math.Data.Fintype.Algebra

@[local simp]
private def pi_add [Add R] : ∀{ι} (a b: ι -> R) (x: ι), (a + b) x = a x + b x :=
   fun _ _ _ => rfl

def QuadraticForm.ofNonnegSignature [SemiringOps R] [IsSemiring R] [IsCommMagma R] (z p: ℕ) : QuadraticForm R (Fin (z + p) -> R) where
  toFun v :=
    ∑x: Fin p,
      let x := x.natAdd z
      v x * v x
  toFun_smul a v := by
    dsimp
    rw [smul_eq_mul, mul_sum]
    congr; ext i
    simp [SMul.smul]
    ac_rfl
  exists_companion' := by
    refine ⟨?_, ?_⟩
    apply BilinMap.mk (fun a b =>
      ∑x: Fin p, 2 * a (x.natAdd z) * b (x.natAdd z))
    · intro a b k
      rw [sum_add_sum]
      congr; ext i
      rw [←add_mul, ←mul_add]
      rfl
    · intro k a b
      rw [sum_add_sum]
      congr; ext i
      rw [←mul_add]
      rfl
    · intro r a k
      simp [mul_sum]
      congr; ext i
      rw [←mul_assoc, mul_left_comm]
      ac_rfl
    · intro r a k
      simp [mul_sum]
      congr; ext i
      rw [mul_left_comm]
    · intro a b
      simp [DFunLike.coe, BilinMap.mk]
      rw [sum_add_sum, sum_add_sum]
      congr; ext i
      simp [add_mul, mul_add, two_mul]
      ac_nf

def QuadraticForm.ofSignature [RingOps R] [IsRing R] [IsCommMagma R] (z p n: ℕ) : QuadraticForm R (Fin (z + p + n) -> R) where
  toFun v :=
     (∑x: Fin p,
    let x := (x.natAdd z).castAdd n
    v x * v x) -
     (∑x: Fin n,
    let x := x.natAdd (z + p)
    (v x * v x))
  toFun_smul a v := by
    dsimp
    rw [smul_eq_mul, mul_sub, mul_sum, mul_sum]
    congr
    iterate 2
    ext i
    simp [smul_eq_mul]
    ac_nf
  exists_companion' := by
    refine ⟨?_, ?_⟩
    apply BilinMap.mk (fun a b =>
      2 * (
       (∑x: Fin p,
      let x := (x.natAdd z).castAdd n
      a x * b x) -
       (∑x: Fin n,
      let x := x.natAdd (z + p)
      (a x * b x))))
    · intro a b k
      simp
      rw [←mul_add]; congr 1
      conv => {
        rhs; rw [sub_eq_add_neg, sub_eq_add_neg,
          add_assoc, add_left_comm (-_),
          ←neg_add_rev, ←add_assoc,
          sum_add_sum, sum_add_sum, ←sub_eq_add_neg]
      }
      congr
      · ext i
        rw [add_mul]
      · ext i
        rw [add_mul, add_comm]
    · intro a b k
      simp
      rw [←mul_add]; congr 1
      conv => {
        rhs; rw [sub_eq_add_neg, sub_eq_add_neg,
          add_assoc, add_left_comm (-_),
          ←neg_add_rev, ←add_assoc,
          sum_add_sum, sum_add_sum, ←sub_eq_add_neg]
      }
      congr
      · ext i
        rw [mul_add]
      · ext i
        rw [mul_add, add_comm]
    · intro r a k
      rw [smul_eq_mul, mul_left_comm, mul_sub r, mul_sum, mul_sum]
      congr
      · ext i
        simp
        rw [←mul_assoc]
      · ext i
        simp
        rw [←mul_assoc]
    · intro r a k
      rw [smul_eq_mul, mul_left_comm, mul_sub r, mul_sum, mul_sum]
      congr
      · ext i
        simp
        ac_nf
      · ext i
        simp
        ac_nf
    · intro a b
      simp [BilinMap.mk, DFunLike.coe]

      conv => {
        rhs; simp [sub_eq_add_neg]
      }
      ac_nf
      -- FIXME: finish this proof
      sorry

def QuadraticForm.ofSignature' [RingOps R] [IsRing R] [IsCommMagma R] (z p n: ℕ) (k: ℕ) (keq: k = z + p + n) : QuadraticForm R (Fin k -> R) where
  toFun v := QuadraticForm.ofSignature z p n (fun x => v (x.cast keq.symm))
  toFun_smul a v := by
    dsimp
    apply QuadraticMap.toFun_smul
  exists_companion' := by
    subst k
    apply QuadraticMap.exists_companion
