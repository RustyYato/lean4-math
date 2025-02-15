import Math.Topology.MetricSpace.Abs
import Math.Topology.MetricSpace.Basic
import Math.Algebra.Impls.Real
import Math.Data.Real.OrderedAlgebra

instance : Dist ℝ ℝ := Abs.instDist _
instance : IsMetricSpace ℝ := Abs.instIsMetricSpace _
instance : Topology ℝ := Topology.ofIsPseudoMetricSpace
instance : Topology (ℝ × ℝ) := Topology.ofIsPseudoMetricSpace

instance instContℝxℝfst : Topology.IsContinuous (fun x: ℝ×ℝ => x.1) where
  isOpen_preimage S Sopen := by
    intro x hx
    have ⟨δ, δ_pos, ball_sub⟩ := Sopen _ hx
    refine ⟨δ, δ_pos, ?_⟩
    intro y hy
    apply ball_sub
    simp [IsPseudoMetricSpace.Ball, dist] at *
    rw [←add_zero (dist _ _)]
    apply lt_of_le_of_lt _ hy
    apply add_le_add
    rfl
    apply dist_nonneg

instance instContℝxℝsnd : Topology.IsContinuous (fun x: ℝ×ℝ => x.2) where
  isOpen_preimage S Sopen := by
    intro x hx
    have ⟨δ, δ_pos, ball_sub⟩ := Sopen _ hx
    refine ⟨δ, δ_pos, ?_⟩
    intro y hy
    apply ball_sub
    simp [IsPseudoMetricSpace.Ball, dist] at *
    rw [←zero_add (dist _ _)]
    apply lt_of_le_of_lt _ hy
    apply add_le_add
    apply dist_nonneg
    rfl

instance instContℝxℝmk
  (f g: ℝ -> ℝ)
  [hf: Topology.IsContinuous f]
  [hg: Topology.IsContinuous g] :
  Topology.IsContinuous (fun x: ℝ => (f x, g x)) where
  isOpen_preimage S Sopen := by
    intro ε hε
    replace hε: (f ε, g ε) ∈ S := hε
    have ⟨δ₀, δ₀_pos, hf⟩ := hf.isOpen_preimage (S.image Prod.fst) ?_ ε (by
      rw [Set.mem_preimage, Set.mem_image]
      exists (f ε, g ε))
    have ⟨δ₁, δ₁_pos, hg⟩ := hg.isOpen_preimage (S.image Prod.snd) ?_ ε (by
      rw [Set.mem_preimage, Set.mem_image]
      exists (f ε, g ε))
    refine ⟨min δ₀ δ₁, ?_, ?_⟩
    · apply lt_min_iff.mpr; apply And.intro <;> assumption
    · intro x hx
      have hfx := hf x (IsPseudoMetricSpace.ball_sub _ _ _ (min_le_left _ _) _ hx)
      have hgx := hg x (IsPseudoMetricSpace.ball_sub _ _ _ (min_le_right _ _) _ hx)


      sorry
    · intro _ ⟨α, hα, h⟩; subst h
      have ⟨δ, δ_pos, ball_sub⟩ := Sopen α hα
      refine ⟨_, δ_pos, ?_⟩
      intro x hx
      rw [Set.mem_image]
      refine ⟨(α.fst, x), ?_, rfl⟩
      apply ball_sub
      simp [IsPseudoMetricSpace.Ball, dist] at *
      rw [dist_self, zero_add]
      assumption
    · intro _ ⟨α, hα, h⟩; subst h
      have ⟨δ, δ_pos, ball_sub⟩ := Sopen α hα
      refine ⟨_, δ_pos, ?_⟩
      intro x hx
      rw [Set.mem_image]
      refine ⟨(x, α.snd), ?_, rfl⟩
      apply ball_sub
      simp [IsPseudoMetricSpace.Ball, dist] at *
      rw [dist_self, add_zero]
      assumption

instance (f: ℝ × ℝ -> ℝ) (a: ℝ) [hf: Topology.IsContinuous f]
  : Topology.IsContinuous (fun x: ℝ => f (a, x)) where
  isOpen_preimage S Sopen := by
    intro ε ε_mem
    have ⟨δ, δ_pos, ball_sub⟩ := hf.isOpen_preimage S Sopen _ ε_mem
    refine ⟨δ, δ_pos, ?_⟩
    intro x hx
    apply ball_sub
    simp [IsPseudoMetricSpace.Ball, dist]
    rw [dist_self, zero_add]
    assumption

instance (f: ℝ × ℝ -> ℝ) (a: ℝ) [hf: Topology.IsContinuous f]
  : Topology.IsContinuous (fun x: ℝ => f (x, a)) where
  isOpen_preimage S Sopen := by
    intro ε ε_mem
    have ⟨δ, δ_pos, ball_sub⟩ := hf.isOpen_preimage S Sopen _ ε_mem
    refine ⟨δ, δ_pos, ?_⟩
    intro x hx
    apply ball_sub
    simp [IsPseudoMetricSpace.Ball, dist]
    rw [dist_self, add_zero]
    assumption

instance instContℝadd : Topology.IsContinuous (fun x: ℝ × ℝ => x.1 + x.2) where
  isOpen_preimage S Sopen := by
    intro ε ε_mem
    have ⟨δ, δ_pos, ball_sub⟩  := Sopen _ ε_mem
    refine ⟨δ, δ_pos, ?_⟩
    intro x hx
    apply ball_sub
    dsimp
    unfold IsPseudoMetricSpace.Ball dist instDistProdOfAdd at *
    rw [Set.mk_mem] at *
    replace hx : ‖_‖ + ‖_‖ < _ := hx
    show ‖_‖ < _
    rw [sub_eq_add_neg, neg_add_rev, add_assoc, ←add_assoc ε.snd, ←sub_eq_add_neg ε.snd,
      add_comm _ (-_), ←add_assoc, ←sub_eq_add_neg]
    apply lt_of_le_of_lt
    apply abs_add_le_add_abs
    assumption

instance (f g: ℝ -> ℝ) [Topology.IsContinuous f] [Topology.IsContinuous g] : Topology.IsContinuous (fun x: ℝ => f x + g x) :=
  Topology.IsContinuous.comp (fun x => (f x, g x)) (fun x: ℝ × ℝ => x.1 + x.2)
instance (a: ℝ) : Topology.IsContinuous (fun x: ℝ => a + x) :=
  inferInstanceAs (
    Topology.IsContinuous <|
      (fun x: ℝ × ℝ => x.1 + x.2) ∘
      (fun x => (a, (fun x => x) x))
  )
instance (a: ℝ) : Topology.IsContinuous (fun x: ℝ => x + a) :=
  inferInstanceAs (
    Topology.IsContinuous <|
      (fun x: ℝ × ℝ => x.1 + x.2) ∘
      (fun x => ((fun x => x) x, a))
  )

variable {a: ℝ}

#synth Topology.IsContinuous (fun x: ℝ => 3 + x + 2 + x)

instance : Topology.IsContinuous (fun x: ℝ × ℝ => x.1 * x.2) where
  isOpen_preimage S Sopen := by
    sorry
