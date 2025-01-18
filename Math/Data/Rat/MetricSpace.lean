import Math.Topology.MetricSpace.Basic
import Math.Topology.Constructions
import Math.Data.Rat.OrderedAlgebra

instance : Dist ℚ ℚ where
  dist a b := ‖a - b‖

instance : IsMetricSpace ℚ where
  dist_self := by
    intro x
    show ‖_‖ = _
    rw [sub_self]
    rfl
  dist_comm := by
    intro a b
    show ‖_‖ = _
    rw [Rat.abs_sub_comm]
    rfl
  dist_triangle := by
    intro a b k
    show ‖_‖ ≤ ‖_‖ + ‖_‖
    rw [←sub_zero (a - b), ←sub_self k, sub_sub, sub_eq_add_neg a, add_assoc,
      add_comm a, sub_eq_add_neg, add_assoc, add_comm (-b), ←sub_eq_add_neg, ←sub_eq_add_neg, add_comm]
    apply Rat.abs_add_le_add_abs
  of_dist_eq_zero := by
    intro a b eq
    have := Rat.eq_zero_iff_abs_eq_zero.mpr eq
    exact eq_of_sub_eq_zero _ _ this

instance : Topology ℚ := Topology.ofIsPseudoMetricSpace
instance (priority := 2000) rat_prod_topo : Topology (ℚ × ℚ) := Topology.ofIsPseudoMetricSpace

example : rat_prod_topo ≤ Topology.topo_product := by
  intro S mem
  apply mem.map (f := id) (tb := rat_prod_topo)
  intro s hs
  conv at hs => {
    unfold sSup instSupSetSet
    dsimp
    erw [Set.image_pair, Set.sUnion_pair]
  }
  cases hs <;> rename_i hs
  · obtain ⟨s', s'_open, eq⟩ := hs
    subst s
    rw [Set.preimage_preimage, Function.comp_id]
    intro x hx
    obtain ⟨δ, δ_pos, sub⟩ := s'_open _ hx
    refine ⟨δ, δ_pos, ?_⟩
    intro y hy
    apply sub
    show ‖_‖ < δ
    replace hy : ‖_‖ + ‖_‖ < δ := hy
    apply lt_of_le_of_lt _ hy
    apply Rat.le_add_right_nonneg
    apply Rat.abs_nonneg
  · obtain ⟨s', s'_open, eq⟩ := hs
    subst s
    rw [Set.preimage_preimage, Function.comp_id]
    intro x hx
    obtain ⟨δ, δ_pos, sub⟩ := s'_open _ hx
    refine ⟨δ, δ_pos, ?_⟩
    intro y hy
    apply sub
    show ‖_‖ < δ
    replace hy : ‖_‖ + ‖_‖ < δ := hy
    apply lt_of_le_of_lt _ hy
    apply Rat.le_add_left_nonneg
    apply Rat.abs_nonneg

instance : Topology.IsContinuous (Prod.fst (α := ℚ) (β := ℚ)) where
  isOpen_preimage := by
    intro s sopen
    intro x mem
    replace mem: x.fst ∈ s := mem
    obtain ⟨δ, δ_pos, sub⟩  := sopen _ mem
    refine ⟨_, δ_pos, ?_⟩
    intro y hy
    apply sub
    show ‖x.fst - _‖ < δ
    apply lt_of_le_of_lt _ hy
    apply Rat.le_add_right_nonneg
    apply dist_nonneg

instance : Topology.IsContinuous (Prod.snd (α := ℚ) (β := ℚ)) where
  isOpen_preimage := by
    intro s sopen
    intro x mem
    replace mem: x.snd ∈ s := mem
    obtain ⟨δ, δ_pos, sub⟩  := sopen _ mem
    refine ⟨_, δ_pos, ?_⟩
    intro y hy
    apply sub
    show ‖x.snd - _‖ < δ
    apply lt_of_le_of_lt _ hy
    apply Rat.le_add_left_nonneg
    apply dist_nonneg

instance Rat.mk_prod_continuous (f: ℚ -> ℚ) (g: ℚ -> ℚ)
  [cf: Topology.IsContinuous f]
  [cg: Topology.IsContinuous g]: Topology.IsContinuous (fun x: ℚ => (f x, g x)) where
  isOpen_preimage := by
    intro S S_open x mem
    rw [Set.mem_preimage] at mem
    have ⟨δ, δ_pos, sub⟩ := S_open _ mem
    have ⟨δ₀, δ₀_pos, sub₀⟩ := cf.isOpen_preimage (IsPseudoMetricSpace.Ball (f x) (δ /? 2)) Topology.IsOpen.Ball x (by
      show dist (f x) (f x) < δ /? 2
      rw [dist_self]
      apply div_pos
      assumption
      trivial)
    have ⟨δ₁, δ₁_pos, sub₁⟩ := cg.isOpen_preimage (IsPseudoMetricSpace.Ball (g x) (δ /? 2)) Topology.IsOpen.Ball x (by
      show dist (g x) (g x) < δ /? 2
      rw [dist_self]
      apply div_pos
      assumption
      trivial)
    refine ⟨min δ₀ δ₁, ?_, ?_⟩
    apply lt_min_iff.mpr
    apply And.intro
    assumption
    assumption
    intro y hy
    apply sub
    dsimp
    show ‖_‖ + ‖_‖ < δ
    dsimp
    replace hy : ‖_‖ < min δ₀ δ₁ := hy
    rw [lt_min_iff] at hy
    have := sub₀  _  hy.left
    have := sub₁  _  hy.right
    rw [Rat.add_half δ]
    apply add_lt_add
    assumption
    assumption

def Rat.continuous_lemma (f: ℚ -> ℚ)
  (h: ∀ε > (0: ℚ), ∃δ > 0, ∀x₀ x₁: ℚ, ‖x₀ - x₁‖ < δ -> ‖f x₀ - f x₁‖ < ε) : Topology.IsContinuous f where
  isOpen_preimage := by
    intro s so x mem
    replace mem: f x ∈ s := mem
    obtain ⟨ε, ε_pos, ball_sub⟩ := so _ mem
    replace ⟨δ, δ_pos, h⟩ := h ε ε_pos
    refine ⟨δ, δ_pos, ?_⟩
    intro y hy
    apply ball_sub
    apply h
    assumption

instance Rat.add_continuous : Topology.IsContinuous (fun x: ℚ × ℚ => x.fst + x.snd) where
  isOpen_preimage := by
    intro S S_open x mem
    have ⟨δ, δ_pos, sub⟩  := S_open _ mem
    refine ⟨δ, δ_pos, ?_⟩
    intro y hy
    apply sub
    dsimp
    show ‖_‖ < δ
    rw [sub_eq_add_neg, neg_add_rev, add_assoc, ←add_assoc x.snd, add_comm _ (-y.fst), ←add_assoc]
    apply lt_of_le_of_lt
    apply abs_le_abs_add_abs
    rw [←sub_eq_add_neg, ←sub_eq_add_neg]
    assumption

instance Rat.mul_continuous_left (x: ℚ) : Topology.IsContinuous (· * x) where
  isOpen_preimage := by
    if hx:x = 0 then
      have : Topology.IsContinuous (· * x) := by
        conv => { arg 1; intro x; rw [hx, mul_zero] }
        infer_instance
      apply this.isOpen_preimage
    else
    intro s o a h
    replace h: a * x ∈ s := h
    obtain ⟨d, d_pos, ball⟩ := o (a * x) h
    refine ⟨d /? ‖x‖, ?_, ?_⟩
    apply Rat.div_pos
    assumption
    apply lt_of_le_of_ne
    apply Rat.abs_nonneg
    symm
    intro g
    cases Rat.eq_zero_iff_abs_eq_zero.mpr g
    contradiction
    intro b mem
    apply ball (b * x)
    show ‖_‖ < d
    rw [←sub_mul, mul_abs]
    apply Rat.lt_of_mul_lt_mul_right_pos
    apply (Rat.inv_pos ‖x‖ _).mp
    apply lt_of_le_of_ne
    apply Rat.abs_nonneg
    symm
    repeat
      intro g
      cases Rat.eq_zero_iff_abs_eq_zero.mpr g
      contradiction
    rw [mul_assoc, mul_inv?_cancel, mul_one, ←div_eq_mul_inv?]
    assumption

instance Rat.mul_continuous_right (x: ℚ) : Topology.IsContinuous (x * ·) := by
  conv => { arg 1; intro; rw [mul_comm] }
  infer_instance

def Rat.add_continuous' (f g: ℚ -> ℚ) (cf: Topology.IsContinuous f) (cg: Topology.IsContinuous g) : Topology.IsContinuous (fun x => f x + g x) :=
  (Rat.mk_prod_continuous f g).comp' Rat.add_continuous

def Rat.mul_continuous (f g: ℚ -> ℚ) (cf: Topology.IsContinuous f) (cg: Topology.IsContinuous g) : Topology.IsContinuous (fun x => f x * g x) where
  isOpen_preimage := sorry

instance (f g: ℚ -> ℚ) [cf: Topology.IsContinuous f] [cg: Topology.IsContinuous g] : Topology.IsContinuous (fun x => f x + g x) :=
  Rat.add_continuous' f g cf cg

instance (f g: ℚ -> ℚ) [cf: Topology.IsContinuous f] [cg: Topology.IsContinuous g] : Topology.IsContinuous (fun x => f x * g x) :=
  Rat.mul_continuous f g cf cg

instance Rat.add_continuous_left (x: ℚ) : Topology.IsContinuous (· + x) := inferInstance
instance Rat.add_continuous_right (x: ℚ) : Topology.IsContinuous (x + ·) :=
  Rat.add_continuous' (fun _ => x) (fun x => x) inferInstance inferInstance
