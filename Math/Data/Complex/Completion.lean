import Math.Data.Complex.Norm
import Math.Data.Rsqrtd.Hom

notation "ℚ[i]" => @Rsqrtd ℚ (-1)

private def toℂ : ℚ[i] ↪+* ℂ :=
  Rsqrtd.liftEmbedding Rat.castHom

noncomputable instance : Norm ℚ[i] ℝ where
  norm x := ‖toℂ x‖

@[simp] def toℂ_real (x: ℚ[i]) : (toℂ x).real = x.a := rfl
@[simp] def toℂ_img (x: ℚ[i]) : (toℂ x).img = x.b := rfl

private def norm_def (q: ℚ[i]) : ‖q‖ = ‖toℂ q‖ := rfl

instance : IsAlgebraNorm ℚ[i] where
  norm_zero_iff {a} := by rw [norm_def, norm_zero_iff, ←map_zero toℂ, toℂ.inj.eq_iff]
  norm_one := by rw [norm_def, map_one, norm_one]
  norm_neg _ := by rw [norm_def, map_neg, norm_neg]; rfl
  norm_mul _ _ := by rw [norm_def, map_mul, norm_mul]; rfl
  norm_add_le_add_norm a b := by
    rw [norm_def, map_add]
    apply norm_add_le_add_norm

abbrev ℝi := Cauchy ℚ[i]

private def mk_grat : ℚ -> ℚ -> ℚ[i] := Rsqrtd.mk

namespace ℝi

def i : ℝi := .of ⟨0, 1⟩
def i_sq_eq_neg_one : i ^ 2 = -1 := rfl

def rat_cast_abs_eq_abs_rat_cast (a: ℚ) : (|a|: ℚ) = (|a|: ℝ) := by
  apply le_antisymm
  apply le_max_iff.mpr
  rw [abs_def]
  split; left; rfl
  right; rfl
  apply max_le
  rw [abs_def]
  split
  rfl; apply le_neg_of_nonpos
  apply le_of_not_le
  rwa [←ratCast_zero, Real.ofRat_le]
  rw [abs_def]
  split
  apply neg_le_of_nonneg
  rwa [←ratCast_zero, Real.ofRat_le]
  rfl

def real.spec (x y: CauchySeq ℚ[i]) (h: x ≈ y) :
  CauchySeq.is_cauchy_equiv (fun i => (x i).a) (fun i => (y i).a) := by
  intro ε εpos
  simp
  replace ⟨δ, h⟩ := h ε (Real.ofRat_lt.mpr εpos)
  exists δ
  intro n m hn hm
  replace h := h n m hn hm
  simp at h
  apply Real.ofRat_lt.mp
  apply lt_of_le_of_lt _ h
  show (|(x n).a - (y m).a|: ℚ) ≤ ‖x n - y m‖
  rw [norm_def, map_sub, Complex.norm_def]
  apply flip le_trans
  apply (map_le NNReal.orderEmbedReal).mp
  apply NNReal.sqrt_strictMonotone.le_iff_le.mpr
  apply le_add_right
  apply bot_le
  show _ ≤ NNReal.embedReal _
  rw [NNReal.sqrt_square]
  simp
  show _ ≤ |Rat.castHom _ - Rat.castHom _|
  rw [←map_sub, rat_cast_abs_eq_abs_rat_cast]
  rfl

def img.spec (x y: CauchySeq ℚ[i]) (h: x ≈ y) :
  CauchySeq.is_cauchy_equiv (fun i => (x i).b) (fun i => (y i).b) := by
  intro ε εpos
  simp
  replace ⟨δ, h⟩ := h ε (Real.ofRat_lt.mpr εpos)
  exists δ
  intro n m hn hm
  replace h := h n m hn hm
  simp at h
  apply Real.ofRat_lt.mp
  apply lt_of_le_of_lt _ h
  show (|(x n).b - (y m).b|: ℚ) ≤ ‖x n - y m‖
  rw [norm_def, map_sub, Complex.norm_def]
  apply flip le_trans
  apply (map_le NNReal.orderEmbedReal).mp
  apply NNReal.sqrt_strictMonotone.le_iff_le.mpr
  apply le_add_left
  apply bot_le
  show _ ≤ NNReal.embedReal _
  rw [NNReal.sqrt_square]
  simp
  show _ ≤ |Rat.castHom _ - Rat.castHom _|
  rw [←map_sub, rat_cast_abs_eq_abs_rat_cast]
  rfl

def mk.spec (a b c d: CauchySeq ℚ) (h: a ≈ c) (g: b ≈ d) :
  CauchySeq.is_cauchy_equiv (fun i => mk_grat (a i) (b i)) (fun i => mk_grat (c i) (d i)) := by
  intro ε εpos
  simp
  have ⟨ε', ε'pos, ε'_lt_ε⟩ := Real.exists_rat_between 0 _ (half_pos εpos)
  rw [←ratCast_zero, Real.ofRat_lt] at ε'pos
  replace ⟨δ, h⟩ := (h ε' ε'pos).merge (g ε' ε'pos)
  clear g
  exists δ
  intro n m hn hm
  replace ⟨h, g⟩ := h n m hn hm
  show ‖mk_grat (a n - c m) (b n - d m)‖ < _
  rw [show mk_grat (a n - c m) (b n - d m) =
    mk_grat (a n - c m) 0 + mk_grat 0 (b n - d m) from ?_]
  apply lt_of_le_of_lt
  apply norm_add_le_add_norm
  rw [←add_half ε]
  apply add_lt_add
  · apply lt_of_le_of_lt _ ε'_lt_ε
    rw [norm_def, mk_grat, Complex.norm_def]
    simp
    rw [ratCast_zero, NNReal.square_zero, add_zero, NNReal.sqrt_square]
    simp
    rw [←rat_cast_abs_eq_abs_rat_cast, Real.ofRat_le]
    apply le_of_lt; assumption
  · apply lt_of_le_of_lt _ ε'_lt_ε
    rw [norm_def, mk_grat, Complex.norm_def]
    simp
    rw [ratCast_zero, NNReal.square_zero, zero_add, NNReal.sqrt_square]
    simp
    rw [←rat_cast_abs_eq_abs_rat_cast, Real.ofRat_le]
    apply le_of_lt; assumption
  show Rsqrtd.mk _ _ = Rsqrtd.mk _ _ + Rsqrtd.mk _ _
  ext <;> simp

def real : ℝi -> ℝ := by
  refine Quotient.lift ?_ ?_
  intro x
  exact Cauchy.ofSeq {
    seq i := (x i).a
    is_cacuhy := by
      apply real.spec
      rfl
  }
  intro a b h
  apply Quotient.sound
  apply real.spec
  assumption

def img : ℝi -> ℝ := by
  refine Quotient.lift ?_ ?_
  intro x
  exact Cauchy.ofSeq {
    seq i := (x i).b
    is_cacuhy := by
      apply img.spec
      rfl
  }
  intro a b h
  apply Quotient.sound
  apply img.spec
  assumption

def mk : ℝ -> ℝ -> ℝi := by
  refine Quotient.lift₂ ?_ ?_
  intro a b
  exact Cauchy.ofSeq {
    seq := fun i => mk_grat (a i) (b i)
    is_cacuhy := by
      apply mk.spec
      rfl
      rfl
  }
  intro a b c d ac bd
  apply Quotient.sound
  apply mk.spec
  assumption
  assumption

@[simp] def mk_real_img (x: ℝi) : mk x.real x.img = x := by
  induction x using Cauchy.ind
  apply Quotient.sound
  apply CauchySeq.pointwise
  intro i
  rfl
@[simp] def mk_real (a b: ℝ) : (mk a b).real = a := by
  induction a, b using Cauchy.ind₂
  apply Quotient.sound
  apply CauchySeq.pointwise
  intro i
  rfl
@[simp] def mk_img (a b: ℝ) : (mk a b).img = b := by
  induction a, b using Cauchy.ind₂
  apply Quotient.sound
  apply CauchySeq.pointwise
  intro i
  rfl

def mk_mul (a b c d: ℝ) : mk a b * mk c d = mk (a * c - b * d) (a * d + b * c) := by
  induction a, b using Cauchy.ind₂ with | ofSeq a b =>
  induction c, d using Cauchy.ind₂ with | ofSeq c d =>
  apply Quotient.sound
  apply CauchySeq.pointwise
  intro j
  show Rsqrtd.mk _ _ * Rsqrtd.mk _ _ = mk_grat _ _
  show _ = Rsqrtd.mk _ _
  ext <;> simp
  rw [sub_eq_add_neg, neg_mul]
  rfl
  rfl

def mk_add (a b c d: ℝ) : mk a b + mk c d = mk (a + c) (b + d) := by
  induction a, b using Cauchy.ind₂
  induction c, d using Cauchy.ind₂
  rfl

end ℝi

-- show that the complex numbers are the completion of the gaussian rationals
def equivℂ : ℝi ≃+* ℂ where
  toFun x := .mk x.real x.img
  invFun x := .mk x.real x.img
  leftInv _ := by simp
  rightInv _ := by simp; rfl
  map_zero := rfl
  map_one := rfl
  map_add {x y} := by
    rw [←ℝi.mk_real_img x, ←ℝi.mk_real_img y,
      ℝi.mk_add]
    ext <;> simp
  map_mul {x y} := by
    rw [←ℝi.mk_real_img x, ←ℝi.mk_real_img y,
      ℝi.mk_mul]
    ext <;> simp
