import Math.Topology.MetricSpace.Abs
import Math.Topology.MetricSpace.Basic
import Math.Data.Real.Order
import Math.Topology.Connected.Basic
import Math.Data.Real.Lattice
import Math.Topology.Algebra.Ring
import Math.Topology.Order.Defs

open Topology Classical
namespace Real

open Norm.ofAbs

instance : Dist ℝ ℝ := Norm.instDist _
instance : IsMetric ℝ := Norm.instIsMetric _
instance : Topology ℝ := IsPseudoMetric.toTopology
instance : IsMetricSpace ℝ := inferInstance

-- this proof was adapted from
-- https://math.ucr.edu/~res/math205B-2018/Munkres%20-%20Topology.pdf
instance : Topology.IsConnected ℝ where
  univ_preconnected := by
    suffices prf:∀u v: Set ℝ, Topology.IsOpen u -> Topology.IsOpen v ->
      ⊤ ⊆ u ∪ v ->
      ∀x ∈ u, ∀y ∈ v, x < y -> (u ∩ v).Nonempty by
      intro u v hu hv total ⟨x, hx', hx⟩ ⟨y, hy', hy⟩
      clear hx' hy'
      rw [Set.univ_inter]
      rcases lt_trichotomy x y with g | rfl | g
      have ⟨z, _, _⟩ := prf u v hu hv total x hx y hy g
      exists z
      exists x
      have ⟨z, _, _⟩ := prf v u hv hu ?_ y hy x hx g
      exists z
      rwa [Set.union_comm]
    intro A B hA hB total a ha b hb a_lt_b
    rw [←Set.not_disjoint_iff_nonempty_inter]
    intro h
    replace h := Set.of_sub_empty _  <| h (A ∩ B) (Set.inter_sub_left _ _) (Set.inter_sub_right _ _)
    have disjoint : ∀x, x ∉ A ∩ B := by intro x; rw [h]; intro; contradiction
    simp [Set.mem_inter] at disjoint

    let sub : Type _ := Set.Icc a b
    let A₀: Set sub := Set.mk fun x => x.val ∈ A
    let B₀: Set sub := Set.mk fun x => x.val ∈ B

    have hA₀ : IsOpen A₀ := by exists A
    have hB₀ : IsOpen B₀ := by exists B

    have total₀ : ∀x, x ∈ A₀ ∪ B₀ := by
      intro x
      cases total x True.intro
      left; assumption
      right; assumption

    let S := (A ∩ Set.Icc a b)
    let c := ⨆ S
    have b_in_bdd : b ∈ S.upperBounds := by
      intro x ⟨_, hx⟩
      apply hx.right
    have a_mem : a ∈ S := by
      apply And.intro
      assumption
      apply And.intro
      apply le_refl (α := ℝ)
      apply le_of_lt (α := ℝ)
      assumption
    let c' : sub := ⟨c, by
      rw [Set.mem_Icc]
      apply And.intro
      apply le_csSup
      exists b
      apply And.intro
      assumption
      exact a_mem.right
      apply csSup_le
      exists a
      assumption⟩

    rcases total₀ c' with hc | hc
    · have ⟨δ, δpos, ball⟩ := hA _ hc
      replace ball : Ball c _ ⊆ _ := ball
      have a_le_c : a ≤ c := c'.property.left

      let d := (c + δ /? 2) ⊓ b
      let d': sub := ⟨d, by
        rw [Set.mem_Icc]
        apply And.intro
        apply le_min_iff.mpr
        apply And.intro
        apply le_trans a_le_c
        apply le_add_right
        apply le_of_lt; apply half_pos; assumption
        apply le_of_lt; assumption
        apply min_le_right⟩

      have : c < d := by
        apply lt_min_iff.mpr
        apply And.intro
        rw (occs := [1]) [←add_zero c]
        apply add_lt_add_left
        apply half_pos
        assumption
        apply lt_of_le_of_ne
        apply c'.property.right
        intro h
        rw [h] at ball
        refine disjoint _ (ball b ?_) hb
        rwa [mem_ball, dist_self]

      suffices d ∈ S by
        replace this : d ≤ c := le_csSup ?_ this
        have := not_lt_of_le this
        contradiction
        exists b

      apply And.intro _ d'.property
      apply ball
      rw [mem_ball]
      show dist c (min _ _) < δ
      show |_| < _
      rw [min_def]; split
      rw [add_comm, sub_add, sub_self, zero_sub, abs_neg, abs_of_nonneg]
      rw [div?_eq_mul_inv?]; rw (occs := [2]) [←mul_one δ]
      apply mul_lt_mul_of_pos_left
      apply Real.ofRat_lt.mpr
      decide
      assumption
      apply le_of_lt
      apply half_pos
      assumption
      show |_| < δ
      rw [abs_sub_comm, abs_of_nonneg, sub_lt_iff_lt_add, add_comm]
      rename_i h; rw [not_le] at h
      apply lt_of_lt_of_le
      assumption
      apply add_le_add_left
      apply le_of_lt
      rw [div?_eq_mul_inv?]; rw (occs := [2]) [←mul_one δ]
      apply mul_lt_mul_of_pos_left
      apply Real.ofRat_lt.mpr
      decide
      assumption
      rw [le_sub_iff_add_le, zero_add]
      apply c'.property.right
    · have ⟨δ, δpos, ball⟩ := hB _ hc
      replace ball : Ball c _ ⊆ _ := ball
      have c_le_b : c ≤ b := c'.property.right
      let d := (c - δ) ⊔ a
      let d': sub := ⟨d, by
        rw [Set.mem_Icc]
        apply And.intro
        apply le_max_right
        apply max_le_iff.mpr
        apply And.intro
        rw [sub_le_iff_le_add]
        apply le_trans
        apply c'.property.right
        apply le_add_right
        apply le_of_lt; assumption
        apply le_of_lt; assumption⟩

      have d_in_bdd : d ∈ S.upperBounds := by
        intro x hx
        rw [←not_lt]
        intro g
        refine disjoint _ hx.left (ball x ?_)
        rw [mem_ball]
        show |c - x| < δ
        have x_le_c : x ≤ c := le_csSup ?_ hx
        replace ⟨g, a_lt_x⟩ := max_lt_iff.mp g
        rw [abs_def, if_pos]
        rwa [sub_lt_iff_lt_add, add_comm, ←sub_lt_iff_lt_add]
        rwa [le_sub_iff_add_le, zero_add]
        exists b

      have : c ≤ d := by
        apply csSup_le
        exists a
        assumption

      have : d < c := by
        clear this d_in_bdd
        apply max_lt_iff.mpr
        apply And.intro
        rw (occs := [1]) [sub_lt_iff_lt_add, ←add_zero c];
        apply add_lt_add_left
        assumption
        apply lt_of_le_of_ne
        apply c'.property.left
        intro a_eq_c
        rw [a_eq_c] at ha
        exact disjoint c ha hc

      have := not_le_of_lt this
      contradiction

def iio_open (a: ℝ) : IsOpen (Set.Iio a) := by
  intro x hx
  rw [Set.mem_Iio] at hx
  exists a - x
  apply And.intro
  show _ < _
  rwa [lt_sub_iff_add_lt, zero_add]
  intro y hy
  rw [Set.mem_Iio]; rw [mem_ball] at hy
  replace hy : |_| < a - x := hy
  rw [abs_def] at hy
  split at hy
  rw [←not_le]; intro a_le_y
  rename_i h
  rw [le_sub_iff_add_le, zero_add] at h
  exact lt_irrefl (lt_of_lt_of_le hx (le_trans a_le_y h))
  rw [neg_sub] at hy
  have := add_lt_add_right _ _ x hy
  rwa [sub_add_cancel, sub_add_cancel] at this

def ioi_open (a: ℝ) : IsOpen (Set.Ioi a) := by
  intro x hx
  rw [Set.mem_Ioi] at hx
  exists x - a
  apply And.intro
  show _ < _
  rwa [lt_sub_iff_add_lt, zero_add]
  intro y hy
  rw [Set.mem_Ioi]; rw [mem_ball] at hy
  replace hy : |_| < x - a := hy
  rw [abs_def] at hy
  split at hy
  have := add_lt_add_left _ _ (-x) hy
  rwa [←add_sub_assoc, ←add_sub_assoc,
    neg_add_cancel, zero_sub, zero_sub,
    ←neg_lt_neg_iff] at this
  rw [neg_sub] at hy
  rw [←not_le]; intro a_le_y
  rename_i h; rw [not_le] at h
  rw [sub_lt_iff_lt_add, zero_add] at h
  exact lt_irrefl (lt_trans hx (lt_of_lt_of_le h a_le_y))

def ioo_open (a b: ℝ) : IsOpen (Set.Ioo a b) := by
  apply IsOpen.inter
  apply ioi_open
  apply iio_open

instance : IsOrderTopology ℝ where
  generated_from_intervals := by
    ext s
    apply Iff.intro
    · intro h
      rw [IsOpen.eq_sunion_balls h]
      apply IsOpen.sUnion
      intro S
      simp; rintro a b rfl h
      rcases Or.symm (lt_or_le 0 b) with hb | hb
      · rw [show Ball a b = ∅ from ?_]
        apply IsOpen.empty'
        apply Set.ext_empty
        intro x hx
        simp [mem_ball] at hx
        have := lt_of_le_of_lt (dist_nonneg a x) hx
        have := not_le_of_lt this; contradiction
      · rw [show Ball a b = Set.Ioo (a - b) (a + b) from ?_]
        apply IsOpen.inter
        apply Generate.IsOpen.of
        exists a - b
        left; rfl
        apply Generate.IsOpen.of
        exists a + b
        right; rfl
        ext x
        simp [mem_ball]
        show |_| < _ ↔ _
        rw [abs_def]
        apply Iff.intro
        intro g
        apply And.intro
        split at g <;> rename_i g'
        rwa [sub_lt_iff_lt_add, add_comm, ←sub_lt_iff_lt_add] at g
        rw [neg_sub, sub_lt_iff_lt_add] at g
        rw [not_le, sub_lt_iff_lt_add, zero_add] at g'
        apply lt_of_le_of_lt _ g'
        rw [sub_le_iff_le_add]
        apply le_add_right
        apply le_of_lt
        assumption
        split at g <;> rename_i g'
        rw [le_sub_iff_add_le, zero_add] at g'
        apply lt_of_le_of_lt
        assumption
        rw (occs := [1]) [←add_zero a]
        apply add_lt_add_left
        assumption
        rwa [neg_sub, sub_lt_iff_lt_add, add_comm] at g
        intro ⟨g₀, g₁⟩
        split <;> rename_i h
        rwa [sub_lt_iff_lt_add, add_comm, ←sub_lt_iff_lt_add] at g₀
        rwa [neg_sub, sub_lt_iff_lt_add, add_comm]
    · intro h
      induction h with
      | univ => apply IsOpen.univ
      | inter => apply IsOpen.inter <;> assumption
      | sUnion => apply IsOpen.sUnion <;> assumption
      | of h =>
        obtain ⟨x, h⟩ := h
        rcases h with rfl | rfl
        exact ioi_open x
        exact iio_open x

def ici_closed (a: ℝ) : IsClosed (Set.Ici a) := by
  show IsOpen _
  rw [show (Set.Ici a)ᶜ = Set.Iio a from ?_]
  apply iio_open
  ext x
  simp [Set.mem_compl, not_le]

def iic_closed (a: ℝ) : IsClosed (Set.Iic a) := by
  show IsOpen _
  rw [show (Set.Iic a)ᶜ = Set.Ioi a from ?_]
  apply ioi_open
  ext x
  simp [Set.mem_compl, not_le]

def icc_closed (a b: ℝ) : IsClosed (Set.Icc a b) := by
  show IsOpen _
  rw [show (Set.Icc a b)ᶜ = Set.Iio a ∪ Set.Ioi b from ?_]
  apply IsOpen.union
  apply iio_open
  apply ioi_open
  ext x
  simp [Set.mem_compl, Set.mem_union, not_le, ←not_lt]
  apply Classical.or_iff_not_imp_left.symm

def continuous₂_of_eps_del (f: ℝ×ℝ -> ℝ) (h: ∀(ε: ℝ), 0 < ε -> ∃δ: ℝ, 0 < δ ∧  ∀a b: ℝ×ℝ, dist a b < δ -> dist (f a) (f b) < ε) : IsContinuous f where
  isOpen_preimage := by
    rw [topology_eq_metric (ℝ × ℝ)]
    intro S hS x hx
    have ⟨ε, εpos, ball_sub⟩ := hS _ hx
    replace ⟨δ, δpos, h⟩ := h ε εpos
    exists δ
    apply And.intro; assumption
    intro y hy
    apply ball_sub
    apply h
    assumption

instance instContℝneg : Topology.IsContinuous (fun x: ℝ => -x) where
  isOpen_preimage := by
    intro S hS x hx
    replace hx : -x ∈ S := hx
    have ⟨δ, δpos, h⟩ := hS _ hx
    refine ⟨_, δpos, ?_⟩
    intro a ha
    rw [mem_ball] at ha
    rw [Set.mem_preimage]
    replace ha: ‖_‖ < δ := ha
    rw [←neg_sub_neg] at ha
    replace ha: dist (-a) _ < δ := ha
    rw [dist_comm] at ha
    apply h
    assumption

instance instContℝadd : Topology.IsContinuous (fun x: ℝ × ℝ => x.1 + x.2) := by
  apply continuous₂_of_eps_del
  intro ε εpos
  exists ε /? 2
  apply And.intro
  apply half_pos; assumption
  intro (a, b) (c, d) h
  replace h : max _ _ < _ := h
  simp at *
  show ‖_‖ < _
  rw [sub_add, add_sub_assoc, add_comm, add_sub_assoc, add_comm]
  apply lt_of_le_of_lt
  apply norm_add_le_add_norm
  apply lt_of_le_of_lt
  apply add_le_add
  apply le_max_left
  exact dist b d
  apply le_max_right
  exact dist a c
  apply lt_of_lt_of_le
  apply add_lt_add
  assumption
  assumption
  rw [add_half]

instance instContℝmul : Topology.IsContinuous (fun x: ℝ × ℝ => x.1 * x.2) where
  isOpen_preimage := by
    rw [topology_eq_metric (ℝ × ℝ)]
    intro S hS (a, b) hab
    replace hab : a * b ∈ S := hab
    simp
    have ⟨ε, εpos, ball_sub⟩ := hS _ hab
    let M := ‖a‖ + ‖b‖ + 1
    have one_le_M : 1 ≤ M := by
      apply le_add_left
      apply add_nonneg
      apply norm_nonneg
      apply norm_nonneg
    have : 0 < M := by
      apply flip lt_of_lt_of_le
      assumption
      apply zero_lt_one
    let δ := (ε /? M) ⊓ 1
    refine ⟨δ, ?_, ?_⟩
    · apply lt_min_iff.mpr
      apply And.intro
      apply div?_pos
      assumption
      assumption
      apply zero_lt_one
    intro (c, d) hx
    rw [mem_ball] at hx
    rw [Set.mem_preimage]
    replace hx : max ‖_‖ ‖_‖ < δ := hx
    simp at hx
    rw [max_lt_iff] at hx
    obtain ⟨ha, hb⟩ := hx
    simp
    apply ball_sub
    rw [mem_ball]
    show |_| < _
    rw [←add_zero (a * b), ←neg_add_cancel (a * d),
      ←add_assoc, ←sub_eq_add_neg, ←mul_sub, add_sub_assoc, ←sub_mul]
    apply lt_of_le_of_lt
    apply abs_add_le_add_abs
    rw [abs_mul, abs_mul]
    repeat rw [←norm_eq_abs]
    apply lt_of_le_of_lt
    apply add_le_add
    apply mul_le_mul_of_nonneg_left
    apply le_of_lt; assumption
    apply abs_nonneg
    apply mul_le_mul_of_nonneg_right
    apply le_of_lt; assumption
    apply abs_nonneg
    rw [mul_comm _ δ, ←mul_add]
    unfold δ M
    rw [min_mul]
    apply min_lt_iff.mpr; left
    rw [mul_comm, div?_eq_mul_inv?, mul_left_comm, ←div?_eq_mul_inv?]
    rw (occs := [2]) [←mul_one ε]
    apply mul_lt_mul_of_pos_left
    replace hb : ‖b - d‖ < 1 := by
      apply lt_of_lt_of_le
      assumption
      apply min_le_right
    have : ‖d‖ < ‖b‖ + 1 := by
      rw [←add_zero d, ←sub_self b, ←add_sub_assoc, add_comm, add_sub_assoc]
      apply lt_of_le_of_lt
      apply norm_add_le_add_norm
      rw [norm_sub_comm]
      apply add_lt_add_left
      assumption
    apply lt_of_lt_of_le
    apply mul_lt_mul_of_pos_right
    show _ < ‖a‖ + ‖b‖ + 1
    rw [add_assoc]
    apply add_lt_add_left
    assumption
    apply inv?_pos; assumption
    erw [mul_inv?_cancel]
    assumption
    apply add_nonneg
    apply abs_nonneg
    apply abs_nonneg

instance : IsTopologicalRing ℝ where
instance : IsTopologicalSemiring ℝ where
instance : IsTopologicalAddGroup ℝ where

instance : IsOrderClosed ℝ where
  isClosed_le_prod := by
    have :  (Set.mk fun p: ℝ × ℝ => p.fst ≤ p.snd) = Set.preimage (Set.Ici 0) (fun p : ℝ × ℝ => p.snd - p.fst) := by
      ext
      simp [Set.mem_preimage, le_sub_iff_add_le]
    rw [this]
    apply IsClosed.preimage'
    show IsContinuous <| (fun x: ℝ × ℝ => x.1 - x.2) ∘ fun _ => (_, _)
    apply IsContinuous.comp
    apply ici_closed

end Real
