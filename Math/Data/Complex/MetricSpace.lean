import Math.Data.NNReal.Sqrt
import Math.Algebra.Impls.Complex
import Math.Data.Real.Sqrt
import Math.Topology.Connected.Basic

open NNReal Topology

namespace Complex

noncomputable instance : AbsoluteValue ℂ ℝ where
  abs x := (x.real ^ 2 + x.img ^ 2).sqrt

def norm_sq (c: ℂ) : |c| ^ 2 = c.real ^ 2 + c.img ^ 2 := by
  show (Real.sqrt _) ^ 2 = _
  rw [Real.sqrt_sq]
  apply Real.add_nonneg
  apply Real.square_nonneg
  apply Real.square_nonneg

def Complex.abs_eq (x: ℂ) : NNReal.ofReal |x| = NNReal.sqrt (NNReal.square x.real + NNReal.square x.img) := by
  simp [AbsoluteValue.abs]
  rw [Real.sqrt, embedReal_ofReal]
  congr
  unfold ofReal
  congr
  rw [max_iff_le_right.mp]
  rfl
  apply Real.add_nonneg
  apply Real.square_nonneg
  apply Real.square_nonneg

def Complex.abs_mul' (a b: ℂ) : |a * b| = |a| * |b| := by
  apply ofReal_injOn
  apply Real.sqrt_nonneg
  apply Real.mul_nonneg
  apply Real.sqrt_nonneg
  apply Real.sqrt_nonneg
  rw [ofReal_mul, abs_eq, abs_eq, abs_eq]
  simp  [sqrt_mul]
  congr
  apply Subtype.val_inj
  unfold square
  show (a.real * b.real - a.img * b.img) ^ 2 + (a.real * b.img + a.img * b.real) ^ 2 =
    (a.real ^ 2 + a.img ^ 2) * (b.real ^ 2 + b.img ^ 2)

  simp [mul_add, add_mul, mul_sub, sub_mul, square_sub, mul_npow, npow_two,
    sub_eq_add_neg, neg_add_rev, ←neg_mul_left, ←neg_mul_right, neg_neg]
  ac_nf
  repeat first|rw [add_comm _ (a.img * (a.img * (b.img * b.img)))]|rw [←add_assoc]
  congr 2
  repeat rw [add_assoc]
  congr 1
  repeat first|rw [add_comm _ (a.img * (a.img * (b.real * b.real)))]|rw [←add_assoc]
  repeat rw [add_assoc]
  rw (occs := [2]) [←add_zero (a.img * (a.img * (b.real * b.real)))]
  congr
  rw (occs := [2]) [←add_assoc (-_)]
  rw [neg_add_cancel, zero_add, neg_add_cancel]
  apply Real.sqrt_nonneg
  apply Real.sqrt_nonneg

instance instLawfulAbs : IsLawfulAbs ℂ where
  abs_zero_iff := by
    intro x
    rw [←Real.sqrt_0]
    apply Iff.trans (Real.sqrt_inj _ _)
    apply Iff.intro
    intro h
    replace h := neg_eq_of_add_right h
    have h₀: 0 ≤ x.real ^ 2 := by apply Real.square_nonneg
    have h₁: -x.img ^ 2 ≤ 0 := by
      rw [←Real.neg_le_neg_iff, neg_neg]
      apply Real.square_nonneg
    ext
    rw [←h] at h₁
    apply Real.eq_zero_of_square_eq_zero
    apply le_antisymm
    assumption; apply Real.square_nonneg
    rw [h] at h₀
    apply Real.eq_zero_of_square_eq_zero
    apply le_antisymm
    rw [←Real.neg_le_neg_iff, neg_neg] at h₀
    assumption; apply Real.square_nonneg
    rintro rfl
    rfl
    apply Real.add_nonneg
    apply Real.square_nonneg
    apply Real.square_nonneg
    rfl
  abs_nonneg _ := by apply Real.sqrt_nonneg
  abs_mul := Complex.abs_mul'
  abs_add_le_add_abs a b := by
    show NNReal.sqrt _ ≤ NNReal.sqrt _ + NNReal.sqrt _
    iterate 3 rw [ofReal_add]
    any_goals apply Real.square_nonneg
    simp [ofReal_square]
    apply NNReal.square_strictMonotone.le_iff_le.mp
    rw [NNReal.sqrt_sq]
    simp [square, square_add, NNReal.sqrt_sq]
    show (a.real ^ 2 + 2 * a.real * b.real + b.real ^ 2) + (a.img ^ 2 + 2 * a.img * b.img + b.img ^ 2)
      ≤ (a.real ^ 2 + a.img ^ 2) + _ + (b.real ^ 2 + b.img ^ 2)
    rw [show
      (a.real ^ 2 + 2 * a.real * b.real + b.real ^ 2) + (a.img ^ 2 + 2 * a.img * b.img + b.img ^ 2) =
      (a.real ^ 2 + a.img ^ 2 + (b.real ^ 2 + b.img ^ 2)) + (2 * a.real * b.real + 2 * a.img * b.img) by ac_rfl]
    rw (occs := [2]) [add_comm_right _ _ (b.real ^ 2 + _)]
    apply add_le_add_left
    rw [mul_assoc _ (NNReal.sqrt _), sqrt_mul]
    show _ ≤ 2 * _
    rw [mul_assoc, mul_assoc, ←mul_add]
    apply Real.mul_le_mul_of_nonneg_left (k := 2)
    apply Real.ofRat_le.mpr; decide
    rcases lt_or_le (a.real * b.real + a.img * b.img) 0 with h | h
    apply le_trans
    exact le_of_lt h
    show 0 ≤ NNReal.sqrt _
    apply bot_le
    apply (Real.square_strictMonotoneOn.le_iff_le _ _).mp
    show _ ≤ Subtype.val (_^2: ℝ≥0)
    rw [sqrt_sq]
    show _ ≤ ((a.real ^ 2 + a.img ^ 2) * (b.real ^ 2 + b.img ^ 2))
    · apply Real.cauchy_schwartz
    · show 0 ≤ a.real * b.real + a.img * b.img
      assumption
    show 0 ≤ NNReal.sqrt _
    apply bot_le
  abs_neg := by
    intro a
    rw [←neg_one_mul, Complex.abs_mul']
    rw (occs := [2]) [←one_mul |a|]
    congr
    show Real.sqrt _ = _
    simp [_root_.square_neg]

noncomputable instance : Dist ℂ ℝ where
  dist a b := |a - b|

instance : IsMetric ℂ := Abs.instIsMetric ℂ
instance : Topology ℂ := IsPseudoMetric.toTopology
instance : IsPseudoMetricSpace ℂ := inferInstance
instance : IsMetricSpace ℂ := inferInstance

instance : Topology.IsContinuous Complex.real where
  isOpen_preimage := by
    intro S hS x h
    replace ⟨ε, εpos, h⟩ := hS _ h
    let δ : ℝ≥0 := ⟨ε, le_of_lt εpos⟩
    refine ⟨ε, εpos, ?_⟩
    intro y hy
    apply h
    simp [mem_ball, dist] at *
    show |_| < ε
    apply lt_of_le_of_lt _ hy
    apply flip le_trans
    apply (Real.sqrt_strictMonotoneOn.le_iff_le _ _).mpr
    apply le_add_right
    apply Real.square_nonneg
    apply Real.square_nonneg
    apply Real.add_nonneg
    apply Real.square_nonneg
    apply Real.square_nonneg
    rw [Real.sqrt_of_sq]
    rfl

instance : Topology.IsContinuous Complex.img where
  isOpen_preimage := by
    intro S hS x h
    replace ⟨ε, εpos, h⟩ := hS _ h
    let δ : ℝ≥0 := ⟨ε, le_of_lt εpos⟩
    refine ⟨ε, εpos, ?_⟩
    intro y hy
    apply h
    simp [mem_ball, dist] at *
    show |_| < ε
    apply lt_of_le_of_lt _ hy
    apply flip le_trans
    apply (Real.sqrt_strictMonotoneOn.le_iff_le _ _).mpr
    apply le_add_left
    apply Real.square_nonneg
    apply Real.square_nonneg
    apply Real.add_nonneg
    apply Real.square_nonneg
    apply Real.square_nonneg
    rw [Real.sqrt_of_sq]
    rfl

instance : Topology.IsContinuous (fun (x, y) => Complex.mk x y) where
  isOpen_preimage := by
    rw [topology_eq_metric (ℝ × ℝ)]
    intro S hS (a, b) h
    simp [Set.mem_preimage] at h
    replace ⟨ε, εpos, h⟩ := hS _ h
    let ε' : ℝ≥0 := {
      val := ε
      property := le_of_lt εpos
    }
    have : 0 < (2: ℝ) := two_pos
    refine ⟨ε /? Real.sqrt 2, ?_, ?_⟩
    apply div?_pos
    assumption
    apply sqrt_pos
    apply (lt_max_iff (α := ℝ)).mpr
    left
    exact two_pos (α := ℝ)
    intro (c, d) g
    apply h
    simp
    simp [mem_ball, dist] at *
    replace g := max_lt_iff.mp g
    apply of_ofReal_lt
    rw [Complex.abs_eq]
    simp
    rw [ofReal]; conv in max ε 0 => {
      rw [max_iff_le_right.mp (le_of_lt εpos)] }
    apply (NNReal.npowOrderIso 2 (by decide)).resp_lt.mpr
    show _ ^ 2 < ε' ^ 2
    rw [sqrt_sq]
    simp [square_eq_abs_sq]
    apply lt_of_lt_of_le
    apply add_lt_add
    apply (NNReal.npowOrderIso 2 (by decide)).resp_lt.mp
    show _ < ε' /? (NNReal.sqrt 2)
    show |a - c| < ε /? _ ~(_)
    apply lt_of_lt_of_eq
    exact g.left
    congr
    rw [Real.sqrt_def _ (by apply le_of_lt; assumption)]
    rfl
    apply (NNReal.npowOrderIso 2 (by decide)).resp_lt.mp
    show _ < ε' /? (NNReal.sqrt 2)
    show |b - d| < ε /? _ ~(_)
    apply lt_of_lt_of_eq
    exact g.right
    congr
    rw [Real.sqrt_def _ (by apply le_of_lt; assumption)]
    rfl
    clear g
    show _  ^ 2 + _ ^ 2 ≤ ε' ^ 2
    rw [div?_npow]
    have : NNReal.sqrt 2 ^ 2 = 2 := by rw [sqrt_sq]
    iterate 2 conv in NNReal.sqrt 2 ^ 2 => { rw [this] }
    rw [add_half]

def homeoℝxℝ : ℝ × ℝ ≃ₜ ℂ where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  leftInv _ := rfl
  rightInv _ := rfl

instance : Topology.IsConnected ℂ := Topology.connected_of_ofHom homeoℝxℝ

abbrev mk' : ℝ × ℝ -> ℂ := fun x => ⟨x.1, x.2⟩

@[continuity]
def continuous_mk (f g: ℝ × ℝ -> ℝ) (hf: IsContinuous f) (hg: IsContinuous g) : IsContinuous (fun x : ℝ × ℝ => Complex.mk (f x) (g x)) := by
  show IsContinuous <| (fun x: ℝ × ℝ => Complex.mk x.1 x.2) ∘ (fun x => (f x, g x))
  infer_instance

@[continuity]
def continuous_mk' : IsContinuous mk' := by
  show IsContinuous <| (fun x: ℝ × ℝ => Complex.mk x.1 x.2)
  infer_instance

@[continuity]
def continuous_real [Topology α] (f: α -> ℂ) (hf: IsContinuous f) : IsContinuous (fun x : α => (f x).real) := by
  show IsContinuous <| Complex.real ∘ f
  infer_instance

@[continuity]
def continuous_img [Topology α] (f: α -> ℂ) (hf: IsContinuous f) : IsContinuous (fun x : α => (f x).img) := by
  show IsContinuous <| Complex.img ∘ f
  infer_instance

@[continuity]
def continuous_add [Topology α] (f g: α -> ℂ) (hf: IsContinuous f) (hg: IsContinuous g) : IsContinuous (fun x : α => f x + g x) := by
  show IsContinuous <| Complex.mk' ∘ (fun x: α => (_, _))
  apply IsContinuous.comp'
  continuity
  apply continuous_mk'

@[continuity]
def continuous_neg [Topology α] (f: α -> ℂ) (hf: IsContinuous f) : IsContinuous (fun x : α => - f x) := by
  show IsContinuous <| Complex.mk' ∘ (fun x: α => (_, _))
  apply IsContinuous.comp'
  continuity
  apply continuous_mk'

@[continuity]
def continuous_mul [Topology α] (f g: α -> ℂ) (hf: IsContinuous f) (hg: IsContinuous g) : IsContinuous (fun x : α => f x * g x) := by
  show IsContinuous <| Complex.mk' ∘ (fun x: α => (_, _))
  apply IsContinuous.comp'
  continuity
  apply continuous_mk'

instance : IsTopologicalRing ℂ where
  continuous_add := by
    apply continuous_add
    apply IsContinuous.Prod.fst
    apply IsContinuous.Prod.snd
  continuous_mul := by
    apply continuous_mul
    apply IsContinuous.Prod.fst
    apply IsContinuous.Prod.snd
  continuous_neg := by
    apply continuous_neg
    infer_instance
instance : IsTopologicalSemiring ℂ where
instance : IsTopologicalAddGroup ℂ where

end Complex
