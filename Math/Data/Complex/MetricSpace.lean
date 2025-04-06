import Math.Data.Complex.Norm
import Math.Topology.Connected.Basic

open NNReal Topology

namespace Complex

noncomputable instance : Dist ℂ ℝ := Norm.instDist ℂ
instance : IsMetric ℂ := Norm.instIsMetric ℂ
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
    show NNReal.embedReal (NNReal.abs _) ≤ _
    apply NNReal.orderEmbedReal.resp_le.mp
    simp
    apply NNReal.square_strictMonotone.le_iff_le.mp
    rw [NNReal.sqrt_sq, ←NNReal.square_eq_abs_sq]
    apply le_add_right
    apply bot_le

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
    show NNReal.embedReal (NNReal.abs _) ≤ _
    apply NNReal.orderEmbedReal.resp_le.mp
    simp
    apply NNReal.square_strictMonotone.le_iff_le.mp
    rw [NNReal.sqrt_sq, ←NNReal.square_eq_abs_sq]
    apply le_add_left
    apply bot_le

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
    show ‖mk (a - c) (b - d)‖ < _
    simp [Complex.norm_def]
    show _ < NNReal.embedReal ε'
    apply NNReal.orderEmbedReal.resp_lt.mp
    rw [←lt_iff_of_le_iff NNReal.square_strictMonotone.le_iff_le,
      NNReal.sqrt_sq]
    apply lt_of_lt_of_le
    show _ < ε' ^ 2 /? 2 + ε' ^ 2 /? 2
    apply add_lt_add
    any_goals
      rw [←lt_iff_of_le_iff NNReal.sqrt_strictMonotone.le_iff_le]
      rw [NNReal.sqrt_div?, NNReal.sqrt_of_sq, NNReal.sqrt_square]
      apply NNReal.orderEmbedReal.resp_lt.mpr
      show NNReal.embedReal _ < NNReal.embedReal _
      simp [map_div?, embedReal_sqrt]
    exact g.left
    exact g.right
    rw [←two_mul, mul_div?_cancel]

def homeoℝxℝ : ℝ × ℝ ≃ₜ ℂ where
  toFun x := .mk x.1 x.2
  invFun x := ⟨x.real, x.img⟩
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
