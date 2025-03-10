import Math.Topology.MetricSpace.Abs
import Math.Topology.MetricSpace.Basic
import Math.Data.Real.Div
import Math.Data.Real.OrderedAlgebra

instance : Dist ℝ ℝ := Abs.instDist _
instance : IsMetricSpace ℝ := Abs.instIsMetricSpace _
instance : Topology ℝ := Topology.ofIsPseudoMetricSpace
instance : Topology (ℝ × ℝ) := Topology.ofIsPseudoMetricSpace

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

instance instContℝmul : Topology.IsContinuous (fun x: ℝ × ℝ => x.1 * x.2) where
  isOpen_preimage S Sopen := by
    intro (a, b) mem_s
    replace mem_s : a * b ∈ S := mem_s
    have ⟨δ, δpos, spec⟩  := Sopen (a * b) mem_s
    have : 0 < ‖a‖ + ‖b‖ + 1 := by
      rw [←add_zero 0]
      apply add_lt_add_of_le_of_lt
      rw[←add_zero 0]
      apply add_le_add
      apply IsLawfulAbs.abs_nonneg
      apply IsLawfulAbs.abs_nonneg
      exact zero_lt_one
    let δ₀ := min (δ /? (‖a‖ + ‖b‖ + 1)) 1
    have δ₀pos : 0 < δ₀ := by
      apply lt_min_iff.mpr
      apply And.intro _ zero_lt_one
      rw (occs := [1]) [←mul_zero 0]
      apply Real.mul_pos
      assumption
      apply inv?_pos
      assumption
    have δ₀_lt_one : δ₀ ≤ 1 := by
      apply min_le_right
    refine ⟨δ₀, δ₀pos, ?_⟩
    intro (x, y) h
    apply spec (x * y)
    show ‖_ - _‖ < δ
    rw [←add_zero (a * b), ←neg_add_cancel (a * y), ←add_assoc,
      ←sub_eq_add_neg, add_sub_assoc]
    rw [←sub_mul, ←mul_sub]
    apply lt_of_le_of_lt
    apply abs_add_le_add_abs
    rw [mul_abs, mul_abs]
    apply lt_of_le_of_lt
    apply add_le_add
    apply mul_le_mul_of_nonneg_left
    show ‖_‖ ≤ δ₀
    apply le_of_lt
    apply lt_of_le_of_lt _ h
    rw (occs := [1]) [←zero_add ‖_‖]
    apply add_le_add_right
    apply IsLawfulAbs.abs_nonneg
    apply IsLawfulAbs.abs_nonneg
    apply mul_le_mul_of_nonneg_right
    show ‖_‖ ≤ δ₀
    apply le_of_lt
    apply lt_of_le_of_lt _ h
    rw (occs := [1]) [←add_zero ‖_‖]
    apply add_le_add_left
    apply IsLawfulAbs.abs_nonneg
    apply IsLawfulAbs.abs_nonneg
    have : ‖y‖ ≤ ‖b‖ + ‖b - y‖ := by
      rw [abs_sub_comm]
      rw (occs := [1]) [←zero_add y, ←sub_self b, sub_add_assoc, add_comm _ y, sub_eq_add_neg]
      apply abs_add_le_add_abs
    replace : ‖y‖ < ‖b‖ + 1 := by
      apply lt_of_le_of_lt this
      apply add_lt_add_left
      apply lt_of_lt_of_le _ δ₀_lt_one
      apply lt_of_le_of_lt _ h
      rw (occs := [1]) [←zero_add ‖_‖]
      apply add_le_add_right
      apply IsLawfulAbs.abs_nonneg
    rw [mul_comm, ←mul_add]
    apply lt_of_lt_of_le
    apply mul_lt_mul_of_pos_left
    apply add_lt_add_left
    assumption
    assumption
    rw [←add_assoc]
    apply le_trans
    apply mul_le_mul_of_nonneg_right
    apply min_le_left
    apply le_of_lt; assumption
    rw [div?_mul_cancel]

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

instance : Topology.IsContinuous (fun x: ℝ => (x, x)) where
  isOpen_preimage S Sopen := by
    intro x hx
    rw [Set.mem_preimage] at hx
    obtain ⟨δ, δpos, spec⟩ := Sopen _ hx
    refine ⟨_, half_pos δpos, ?_⟩
    intro y hy
    apply spec
    dsimp
    show _ + _ < δ
    dsimp
    rw [←add_half δ]
    apply add_lt_add
    apply hy
    apply hy

-- instance instContℝxℝmap₂
--   (f g: ℝ × ℝ -> ℝ)
--   [Topology.IsContinuous f]
--   [Topology.IsContinuous g]
--   : Topology.IsContinuous (fun x: ℝ×ℝ => (f x, g x)) where
--   isOpen_preimage S Sopen := by

--     have hf := Topology.IsOpen.preimage f (S.image Prod.fst) (by
--       rintro ε ⟨⟨_, ε₁⟩, hε, rfl⟩
--       have ⟨δ, δpos, ball_sub⟩  := Sopen (ε, ε₁) hε
--       refine ⟨_, δpos, ?_⟩
--       intro y hy
--       rw [Set.mem_image]
--       refine ⟨(y, ε₁), ?_, rfl⟩
--       apply ball_sub
--       show dist _ _ < δ
--       simp [dist]
--       rw [dist_self, add_zero]
--       apply hy)
--     have hg := Topology.IsOpen.preimage g (S.image Prod.snd) (by
--       rintro ε ⟨⟨ε₁, _⟩, hε, rfl⟩
--       have ⟨δ, δpos, ball_sub⟩  := Sopen (ε₁, ε) hε
--       refine ⟨_, δpos, ?_⟩
--       intro y hy
--       rw [Set.mem_image]
--       refine ⟨(ε₁, y), ?_, rfl⟩
--       apply ball_sub
--       show dist _ _ < δ
--       simp [dist]
--       rw [dist_self, zero_add]
--       apply hy)
--     intro x hx
--     rw [Set.mem_preimage] at hx
--     have ⟨δ₀, δ₀pos, ball₀⟩  := hf x (by
--       rw [Set.mem_preimage, Set.mem_image]
--       exact ⟨_, hx, rfl⟩)
--     have ⟨δ₁, δ₁pos, ball₁⟩  := hg x (by
--       rw [Set.mem_preimage, Set.mem_image]
--       exact ⟨_, hx, rfl⟩)
--     refine ⟨min δ₀ δ₁, ?_, ?_⟩
--     apply lt_min_iff.mpr
--     apply And.intro <;> assumption
--     intro x₀ hx₀
--     rw [Set.mem_preimage]
--     sorry

    -- have := ball₀ x₀ ?_
    -- rw [Set.mem_preimage, Set.mem_image] at this
    -- obtain ⟨⟨x₁, x₂⟩, mem₀, rfl⟩ := this
    -- have := ball₁ x₀ ?_
    -- rw [Set.mem_preimage, Set.mem_image] at this
    -- obtain ⟨⟨x₃, x₄⟩, mem₁, rfl⟩ := this










    -- have ⟨δ, δ_pos, ball_sub⟩ := Sopen _ hx
    -- refine ⟨δ, δ_pos, ?_⟩
    -- intro y hy
    -- apply ball_sub
    -- simp [IsPseudoMetricSpace.Ball, dist] at *
    -- rw [←zero_add (dist _ _)]
    -- apply lt_of_le_of_lt _ hy
    -- apply add_le_add
    -- apply dist_nonneg
    -- rfl

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
