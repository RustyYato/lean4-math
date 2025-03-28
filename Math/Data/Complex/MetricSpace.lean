import Math.Data.NNReal.Sqrt
import Math.Algebra.Impls.Complex
import Math.Data.Real.Sqrt
import Math.Topology.Connected.Basic

open NNReal Topology

namespace Complex

noncomputable instance : AbsoluteValue ℂ ℝ≥0 where
  abs x := (square x.real + square x.img).sqrt

def norm_sq (c: ℂ) : ‖c‖ ^ 2 = square c.real + square c.img := sqrt_sq _

instance instLawfulAbs : IsLawfulAbs ℂ where
  abs_zero_iff := by
    intro x
    show NNReal.sqrtEquiv _ = 0 ↔ x = 0
    apply Iff.intro
    intro h
    have : sqrtEquiv.symm (sqrtEquiv (square x.real + square x.img)) =
       sqrtEquiv.symm 0 := by rw [h]
    rw [sqrtEquiv.coe_symm, resp_zero] at this
    have ⟨ha, hb⟩ := NNReal.of_add_eq_zero _ _ this
    ext
    exact of_square_eq_zero ha
    exact of_square_eq_zero hb
    rintro rfl
    simp [resp_zero]
  abs_nonneg _ := by apply bot_le
  abs_mul a b := by
    show NNReal.sqrtEquiv _ = NNReal.sqrtEquiv _ * NNReal.sqrtEquiv _
    rw [←resp_mul]
    simp
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
  abs_add_le_add_abs a b := by
    show NNReal.sqrt _ ≤ NNReal.sqrt _ + NNReal.sqrt _
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
  abs_eq_of_add_eq_zero := by
    intro a b h
    cases neg_eq_of_add_left h; clear h
    show NNReal.sqrt _ = NNReal.sqrt _
    simp [NNReal.square_neg]

noncomputable instance : Dist ℂ ℝ≥0 where
  dist a b := ‖a - b‖

instance : IsMetricSpace ℂ := Abs.instIsMetricSpace ℂ
instance : Topology ℂ := Topology.ofIsPseudoMetricSpace

instance : Topology.IsContinuous Complex.real where
  isOpen_preimage := by
    intro S hS x h
    replace ⟨ε, εpos, h⟩ := hS _ h
    let δ : ℝ≥0 := ⟨ε, le_of_lt εpos⟩
    refine ⟨δ, εpos, ?_⟩
    intro y hy
    apply h
    simp [IsPseudoMetricSpace.mem_ball, dist] at *
    show ‖_‖ < ε
    replace hy : embedReal ‖_‖ < ε := hy
    apply lt_of_le_of_lt _ hy
    rw [←embedReal_abs]
    show orderEmbedReal _ ≤ orderEmbedReal _
    apply NNReal.orderEmbedReal.resp_le.mp
    apply flip le_trans
    apply sqrt_strictMonotone.le_iff_le.mpr
    apply le_add_right
    apply bot_le
    rw [sqrt_square]
    rfl

instance : Topology.IsContinuous Complex.img where
  isOpen_preimage := by
    intro S hS x h
    replace ⟨ε, εpos, h⟩ := hS _ h
    let δ : ℝ≥0 := ⟨ε, le_of_lt εpos⟩
    refine ⟨δ, εpos, ?_⟩
    intro y hy
    apply h
    simp [IsPseudoMetricSpace.mem_ball, dist] at *
    show ‖_‖ < ε
    replace hy : embedReal ‖_‖ < ε := hy
    apply lt_of_le_of_lt _ hy
    rw [←embedReal_abs]
    show orderEmbedReal _ ≤ orderEmbedReal _
    apply NNReal.orderEmbedReal.resp_le.mp
    apply flip le_trans
    apply sqrt_strictMonotone.le_iff_le.mpr
    apply le_add_left
    apply bot_le
    rw [sqrt_square]
    rfl

instance : Topology.IsContinuous (fun (x, y) => Complex.mk x y) where
  isOpen_preimage := by
    rw [Real.topo_prodct_eq_metric]
    intro S hS (a, b) h
    simp [Set.mem_preimage] at h
    replace ⟨ε, εpos, h⟩ := hS _ h
    refine ⟨orderEmbedReal (ε /? (NNReal.sqrt 2)), ?_, ?_⟩
    apply div?_pos
    assumption
    apply sqrt_pos
    exact two_pos
    intro (c, d) g
    apply h
    simp
    simp [IsPseudoMetricSpace.mem_ball, dist] at *
    replace g := max_lt_iff.mp g
    apply (NNReal.npowOrderIso 2 (by decide)).resp_lt.mpr
    show ‖_‖ ^ 2 < ε ^ 2
    rw [norm_sq]
    simp [square_eq_abs_sq]
    apply lt_of_lt_of_le
    apply add_lt_add
    apply (NNReal.npowOrderIso 2 (by decide)).resp_lt.mp
    show _ < ε /? (NNReal.sqrt 2)
    exact g.left
    apply (NNReal.npowOrderIso 2 (by decide)).resp_lt.mp
    show _ < ε /? (NNReal.sqrt 2)
    exact g.right
    clear g
    show _  ^ 2 + _ ^ 2 ≤ ε ^ 2
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
  continuity

@[continuity]
def continuous_neg [Topology α] (f: α -> ℂ) (hf: IsContinuous f) : IsContinuous (fun x : α => - f x) := by
  show IsContinuous <| Complex.mk' ∘ (fun x: α => (_, _))
  apply IsContinuous.comp'
  continuity
  continuity

@[continuity]
def continuous_sub [Topology α] (f g: α -> ℂ) (hf: IsContinuous f) (hg: IsContinuous g) : IsContinuous (fun x : α => f x - g x) := by
  show IsContinuous <| Complex.mk' ∘ (fun x: α => (_, _))
  apply IsContinuous.comp'
  continuity
  continuity

@[continuity]
def continuous_mul [Topology α] (f g: α -> ℂ) (hf: IsContinuous f) (hg: IsContinuous g) : IsContinuous (fun x : α => f x * g x) := by
  show IsContinuous <| Complex.mk' ∘ (fun x: α => (_, _))
  apply IsContinuous.comp'
  continuity
  continuity

@[continuity]
def continuous_natCast [Topology α] (f: α -> ℕ) (hf: IsContinuous f) : IsContinuous (fun x : α => (f x: ℂ)) := by
  apply IsContinuous.comp'
  assumption
  continuity

@[continuity]
def continuous_intCast [Topology α] (f: α -> ℤ) (hf: IsContinuous f) : IsContinuous (fun x : α => (f x: ℂ)) := by
  apply IsContinuous.comp'
  assumption
  continuity

@[continuity]
def continuous_nsmul [Topology α] (f: ℕ × α -> ℂ) (hf: IsContinuous f) : IsContinuous (fun x : ℕ × α => x.1 • f x) := by
  continuity

@[continuity]
def continuous_zsmul [Topology α] (f: ℤ × α -> ℂ) (hf: IsContinuous f) : IsContinuous (fun x : ℤ × α => x.1 • f x) := by
  continuity

end Complex
