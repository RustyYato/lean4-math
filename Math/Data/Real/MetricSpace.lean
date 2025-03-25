import Math.Topology.MetricSpace.Abs
import Math.Topology.MetricSpace.Basic
import Math.Data.Real.Div
import Math.Data.Real.OrderedAlgebra
import Math.Topology.Connected.Basic
import Math.Data.Real.Lattice
import Math.Topology.Constructions

open Topology Classical
open IsPseudoMetricSpace (Ball mem_ball ball_sub)
namespace Real

instance : Dist ℝ ℝ := Abs.instDist _
instance : IsMetricSpace ℝ := Abs.instIsMetricSpace _
instance : Topology ℝ := Topology.ofIsPseudoMetricSpace

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

    have hA₀ : IsOpen[sub] A₀ := by exists A
    have hB₀ : IsOpen[sub] B₀ := by exists B

    have total₀ : ∀x, x ∈ A₀ ∪ B₀ := by
      intro x
      cases total x True.intro
      left; assumption
      right; assumption

    let S := (A ∩ Set.Icc a b)
    let c := sSup S
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
      replace ball : IsPseudoMetricSpace.Ball c _ ⊆ _ := ball
      have a_le_c : a ≤ c := c'.property.left

      let d := (c + δ /? 2) ⊓ b
      let d': sub := ⟨d, by
        rw [Set.mem_Icc]
        apply And.intro
        apply le_inf_iff.mpr
        apply And.intro
        apply le_trans a_le_c
        apply le_add_right
        apply le_of_lt; apply half_pos; assumption
        apply le_of_lt; assumption
        apply inf_le_right⟩

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
        rwa [IsPseudoMetricSpace.mem_ball, dist_self]

      suffices d ∈ S by
        replace this : d ≤ c := le_csSup ?_ this
        have := not_lt_of_le this
        contradiction
        exists b

      apply And.intro _ d'.property
      apply ball
      rw [IsPseudoMetricSpace.mem_ball]
      show dist c (min _ _) < δ
      show ‖_‖ < _
      rw [min_def]; split
      rw [add_comm, sub_add, sub_self, zero_sub, abs_neg, (Real.abs_of_nonneg _).mp]
      rw [div?_eq_mul_inv?]; rw (occs := [2]) [←mul_one δ]
      apply mul_lt_mul_of_pos_left
      assumption
      apply Real.ofRat_lt.mpr
      decide
      apply le_of_lt
      apply half_pos
      assumption
      rw [abs_sub_comm, (Real.abs_of_nonneg _).mp, Real.sub_lt_iff_lt_add, add_comm]
      rename_i h; rw [not_le] at h
      apply lt_of_lt_of_le
      assumption
      apply add_le_add_left
      apply le_of_lt
      rw [div?_eq_mul_inv?]; rw (occs := [2]) [←mul_one δ]
      apply mul_lt_mul_of_pos_left
      assumption
      apply Real.ofRat_lt.mpr
      decide
      rw [Real.le_sub_iff_add_le, zero_add]
      apply c'.property.right
    · have ⟨δ, δpos, ball⟩ := hB _ hc
      replace ball : IsPseudoMetricSpace.Ball c _ ⊆ _ := ball
      have c_le_b : c ≤ b := c'.property.right
      let d := (c - δ) ⊔ a
      let d': sub := ⟨d, by
        rw [Set.mem_Icc]
        apply And.intro
        apply le_sup_right
        apply sup_le_iff.mpr
        apply And.intro
        rw [Real.sub_le_iff_le_add]
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
        rw [IsPseudoMetricSpace.mem_ball]
        show ‖c - x‖ < δ
        have x_le_c : x ≤ c := le_csSup ?_ hx
        replace ⟨g, a_lt_x⟩ := max_lt_iff.mp g
        rw [Real.abs_def, if_pos]
        rwa [Real.sub_lt_iff_lt_add, add_comm, ←Real.sub_lt_iff_lt_add]
        rwa [Real.le_sub_iff_add_le, zero_add]
        exists b

      have : c ≤ d := by
        apply csSup_le
        exists a
        assumption

      have : d < c := by
        clear this d_in_bdd
        apply max_lt_iff.mpr
        apply And.intro
        rw (occs := [1]) [Real.sub_lt_iff_lt_add, ←add_zero c];
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
  rwa [Real.lt_sub_iff_add_lt, zero_add]
  intro y hy
  rw [Set.mem_Iio]; rw [IsPseudoMetricSpace.mem_ball] at hy
  replace hy : ‖_‖ < a - x := hy
  rw [abs_def] at hy
  split at hy
  rw [←not_le]; intro a_le_y
  rename_i h
  rw [Real.le_sub_iff_add_le, zero_add] at h
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
  rwa [Real.lt_sub_iff_add_lt, zero_add]
  intro y hy
  rw [Set.mem_Ioi]; rw [IsPseudoMetricSpace.mem_ball] at hy
  replace hy : ‖_‖ < x - a := hy
  rw [abs_def] at hy
  split at hy
  have := add_lt_add_left _ _ (-x) hy
  rwa [←add_sub_assoc, ←add_sub_assoc,
    neg_add_cancel, zero_sub, zero_sub,
    Real.neg_lt_neg_iff] at this
  rw [neg_sub] at hy
  rw [←not_le]; intro a_le_y
  rename_i h; rw [not_le] at h
  rw [Real.sub_lt_iff_lt_add, zero_add] at h
  exact lt_irrefl (lt_trans hx (lt_of_lt_of_le h a_le_y))

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

def ioo_open (a b: ℝ) : IsOpen (Set.Ioo a b) := by
  apply IsOpen.inter
  apply ioi_open
  apply iio_open

def icc_closed (a b: ℝ) : IsClosed (Set.Icc a b) := by
  show IsOpen _
  rw [show (Set.Icc a b)ᶜ = Set.Iio a ∪ Set.Ioi b from ?_]
  apply IsOpen.union
  apply iio_open
  apply ioi_open
  ext x
  simp [Set.mem_compl, Set.mem_union, not_le, ←not_lt]
  apply Classical.or_iff_not_imp_left.symm

instance : IsContinuous' (α := ℝ × ℝ) (β := ℝ) Topology.ofIsPseudoMetricSpace inferInstance Prod.fst := by
  apply IsContinuous'.mk
  intro S hS (a, b) ha
  replace ha : a ∈ S := ha
  have ⟨δ, δpos, ball⟩ := hS _ ha
  refine ⟨_, δpos, ?_⟩
  intro (c, d) hx
  show c ∈ S
  apply ball
  replace hx :  max _ _ < δ := hx
  exact (max_lt_iff.mp hx).left

instance : IsContinuous' (α := ℝ × ℝ) (β := ℝ) Topology.ofIsPseudoMetricSpace inferInstance Prod.snd := by
  apply IsContinuous'.mk
  intro S hS (a, b) hb
  replace ha : b ∈ S := hb
  have ⟨δ, δpos, ball⟩ := hS _ hb
  refine ⟨_, δpos, ?_⟩
  intro (c, d) hx
  show d ∈ S
  apply ball
  replace hx :  max _ _ < δ := hx
  exact (max_lt_iff.mp hx).right

def topo_prodct_eq_metric : (Topology.topo_product: Topology (ℝ×ℝ)) = Topology.ofIsPseudoMetricSpace := by
  let t': Topology (ℝ × ℝ) := Topology.ofIsPseudoMetricSpace
  apply Topology.IsOpen.inj
  ext S
  simp
  apply Iff.intro
  · intro h
    induction h with
    | univ => apply @IsOpen.univ _ t'
    | inter => apply @IsOpen.inter _ t' <;> assumption
    | sUnion => apply @IsOpen.sUnion _ t' <;> assumption
    | of  =>
      rename_i x hx
      simp at hx
      rcases hx with ⟨t,ht,rfl⟩ | ⟨t,ht,rfl⟩
      apply IsOpen.preimage
      assumption
      apply IsOpen.preimage
      assumption
  · intro hS
    have : S = ⋃(Set.mk fun s: Set (ℝ × ℝ) => (∃x r, s = Ball x r) ∧ s ⊆ S) := by
      ext x
      simp [Set.mem_sUnion]
      apply Iff.intro
      intro hx
      have ⟨δ, δpos, ball_sub⟩ := hS _ hx
      exists Ball x δ
      apply And.intro
      apply And.intro
      exists x.1
      exists x.2
      exists δ
      assumption
      rwa [mem_ball, dist_self]
      intro ⟨_, ⟨⟨a, b, δ, rfl⟩, ball_sub_s⟩, hx⟩
      apply ball_sub_s
      assumption
    rw [this]; clear this
    apply Topology.topo_product.sUnion_open
    rintro _ ⟨⟨x, δ, rfl⟩, hb⟩
    rw [show Ball x δ =
      (Set.mk fun y => dist x.fst y.fst < δ) ∩
      (Set.mk fun y => dist x.snd y.snd < δ)
      from ?_]
    apply Generate.IsOpen.inter
    · apply Generate.IsOpen.of
      simp
      left
      refine ⟨Ball x.1 δ, ?_, ?_⟩
      apply IsOpen.Ball
      rfl

    · apply Generate.IsOpen.of
      simp
      right
      refine ⟨Ball x.2 δ, ?_, ?_⟩
      apply IsOpen.Ball
      rfl

    ext y
    simp [mem_ball, Set.mem_inter]
    apply max_lt_iff

def continuous₂_of_eps_del (f: ℝ×ℝ -> ℝ) (h: ∀(ε: ℝ), 0 < ε -> ∃δ: ℝ, 0 < δ ∧  ∀a b: ℝ×ℝ, dist a b < δ -> dist (f a) (f b) < ε) : IsContinuous f where
  isOpen_preimage := by
    rw [topo_prodct_eq_metric]
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
    rw [IsPseudoMetricSpace.mem_ball] at ha
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
  apply abs_add_le_add_abs
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

instance instContℝsub : Topology.IsContinuous (fun x: ℝ × ℝ => x.1 - x.2) := by
  show IsContinuous (fun x: ℝ × ℝ => x.1 - x.2)
  simp [sub_eq_add_neg]
  show IsContinuous ((fun x: ℝ × ℝ => x.1 + x.2) ∘ (fun x: ℝ × ℝ => (x.1, -x.2)))
  apply Topology.IsContinuous.comp'
  apply IsContinuous.prod_mk
  infer_instance
  show IsContinuous ((-·) ∘ (fun x: ℝ × ℝ => x.2))
  apply Topology.IsContinuous.comp
  infer_instance

instance instContℝsub' : Topology.IsContinuous (fun x: ℝ × ℝ => x.2 - x.1) := by
  show IsContinuous (fun x: ℝ × ℝ => x.2 - x.1)
  conv => {
      arg 1; intro x
      rw [←neg_sub]
  }
  show IsContinuous ((fun x: ℝ => -x) ∘ (fun x: ℝ × ℝ => x.1 - x.2))
  infer_instance

def isClosed_le_prod : IsClosed (Set.mk fun p: ℝ × ℝ => p.1 ≤ p.2) := by
  have :  (Set.mk fun p: ℝ × ℝ => p.fst ≤ p.snd) = Set.preimage (Set.Ici 0) (fun p : ℝ × ℝ => p.snd - p.fst) := by
    ext
    simp [Set.mem_preimage, Real.le_sub_iff_add_le]
  rw [this]
  apply IsClosed.preimage
  apply ici_closed

def isClosed_le (f g: ℝ -> ℝ) [IsContinuous f] [IsContinuous g] :
  IsClosed (Set.mk fun x => f x ≤ g x) := by

  sorry

-- instance instContℝadd : Topology.IsContinuous (fun x: ℝ × ℝ => x.1 + x.2) where
--   isOpen_preimage S Sopen := by
--     intro ε ε_mem
--     have ⟨δ, δ_pos, ball_sub⟩  := Sopen _ ε_mem
--     refine ⟨δ, δ_pos, ?_⟩
--     intro x hx
--     apply ball_sub
--     dsimp
--     rw [IsPseudoMetricSpace.mem_ball] at *
--     rw [Set.mk_mem] at *
--     replace hx : ‖_‖ + ‖_‖ < _ := hx
--     show ‖_‖ < _
--     rw [sub_eq_add_neg, neg_add_rev, add_assoc, ←add_assoc ε.snd, ←sub_eq_add_neg ε.snd,
--       add_comm _ (-_), ←add_assoc, ←sub_eq_add_neg]
--     apply lt_of_le_of_lt
--     apply abs_add_le_add_abs
--     assumption

-- instance instContℝmul : Topology.IsContinuous (fun x: ℝ × ℝ => x.1 * x.2) where
--   isOpen_preimage S Sopen := by
--     intro (a, b) mem_s
--     replace mem_s : a * b ∈ S := mem_s
--     have ⟨δ, δpos, spec⟩  := Sopen (a * b) mem_s
--     have : 0 < ‖a‖ + ‖b‖ + 1 := by
--       rw [←add_zero 0]
--       apply add_lt_add_of_le_of_lt
--       rw[←add_zero 0]
--       apply add_le_add
--       apply abs_nonneg
--       apply abs_nonneg
--       exact zero_lt_one
--     let δ₀ := min (δ /? (‖a‖ + ‖b‖ + 1)) 1
--     have δ₀pos : 0 < δ₀ := by
--       apply lt_min_iff.mpr
--       apply And.intro _ zero_lt_one
--       rw (occs := [1]) [←mul_zero 0]
--       apply Real.mul_pos
--       assumption
--       apply inv?_pos
--       assumption
--     have δ₀_lt_one : δ₀ ≤ 1 := by
--       apply min_le_right
--     refine ⟨δ₀, δ₀pos, ?_⟩
--     intro (x, y) h
--     apply spec (x * y)
--     show ‖_ - _‖ < δ
--     rw [←add_zero (a * b), ←neg_add_cancel (a * y), ←add_assoc,
--       ←sub_eq_add_neg, add_sub_assoc]
--     rw [←sub_mul, ←mul_sub]
--     apply lt_of_le_of_lt
--     apply abs_add_le_add_abs
--     rw [abs_mul, abs_mul]
--     apply lt_of_le_of_lt
--     apply add_le_add
--     apply mul_le_mul_of_nonneg_left
--     show ‖_‖ ≤ δ₀
--     apply le_of_lt
--     apply lt_of_le_of_lt _ h
--     rw (occs := [1]) [←zero_add ‖_‖]
--     apply add_le_add_right
--     apply abs_nonneg
--     apply abs_nonneg
--     apply mul_le_mul_of_nonneg_right
--     show ‖_‖ ≤ δ₀
--     apply le_of_lt
--     apply lt_of_le_of_lt _ h
--     rw (occs := [1]) [←add_zero ‖_‖]
--     apply add_le_add_left
--     apply abs_nonneg
--     apply abs_nonneg
--     have : ‖y‖ ≤ ‖b‖ + ‖b - y‖ := by
--       rw [abs_sub_comm]
--       rw (occs := [1]) [←zero_add y, ←sub_self b, sub_add_assoc, add_comm _ y, sub_eq_add_neg]
--       apply abs_add_le_add_abs
--     replace : ‖y‖ < ‖b‖ + 1 := by
--       apply lt_of_le_of_lt this
--       apply add_lt_add_left
--       apply lt_of_lt_of_le _ δ₀_lt_one
--       apply lt_of_le_of_lt _ h
--       rw (occs := [1]) [←zero_add ‖_‖]
--       apply add_le_add_right
--       apply abs_nonneg
--     rw [mul_comm, ←mul_add]
--     apply lt_of_lt_of_le
--     apply mul_lt_mul_of_pos_left
--     apply add_lt_add_left
--     assumption
--     assumption
--     rw [←add_assoc]
--     apply le_trans
--     apply mul_le_mul_of_nonneg_right
--     apply min_le_left
--     apply le_of_lt; assumption
--     rw [div?_mul_cancel]

-- instance instContℝxℝfst : Topology.IsContinuous (fun x: ℝ×ℝ => x.1) where
--   isOpen_preimage S Sopen := by
--     intro x hx
--     have ⟨δ, δ_pos, ball_sub⟩ := Sopen _ hx
--     refine ⟨δ, δ_pos, ?_⟩
--     intro y hy
--     apply ball_sub
--     simp [IsPseudoMetricSpace.Ball, dist] at *
--     rw [←add_zero (dist _ _)]
--     apply lt_of_le_of_lt _ hy
--     apply add_le_add
--     rfl
--     apply dist_nonneg

-- instance instContℝxℝsnd : Topology.IsContinuous (fun x: ℝ×ℝ => x.2) where
--   isOpen_preimage S Sopen := by
--     intro x hx
--     have ⟨δ, δ_pos, ball_sub⟩ := Sopen _ hx
--     refine ⟨δ, δ_pos, ?_⟩
--     intro y hy
--     apply ball_sub
--     simp [IsPseudoMetricSpace.Ball, dist] at *
--     rw [←zero_add (dist _ _)]
--     apply lt_of_le_of_lt _ hy
--     apply add_le_add
--     apply dist_nonneg
--     rfl

-- instance : Topology.IsContinuous (fun x: ℝ => (x, x)) where
--   isOpen_preimage S Sopen := by
--     intro x hx
--     rw [Set.mem_preimage] at hx
--     obtain ⟨δ, δpos, spec⟩ := Sopen _ hx
--     refine ⟨_, half_pos δpos, ?_⟩
--     intro y hy
--     apply spec
--     dsimp
--     show _ + _ < δ
--     dsimp
--     rw [←add_half δ]
--     apply add_lt_add
--     apply hy
--     apply hy

-- instance instContℝxℝmap₂ (f g: ℝ × ℝ -> ℝ) [Topology.IsContinuous f] [Topology.IsContinuous g] : Topology.IsContinuous (fun x: ℝ×ℝ => (f x, g x)) where
--   isOpen_preimage S Sopen := by
--     intro x hx
--     have ⟨δ, δ_pos, spec⟩ := Sopen _ hx
--     dsimp at spec
--     have ⟨δ₀, δ₀pos, spec₀⟩ := Topology.IsOpen.preimage f (IsPseudoMetricSpace.Ball (f x) (δ /? 2)) Topology.IsOpen.Ball
--       x (by
--       show dist _ _ < δ /? 2
--       rw [dist_self]
--       apply half_pos
--       assumption)
--     have ⟨δ₁, δ₁pos, spec₁⟩ := Topology.IsOpen.preimage g (IsPseudoMetricSpace.Ball (g x) (δ /? 2)) Topology.IsOpen.Ball
--       x (by
--       show dist _ _ < δ /? 2
--       rw [dist_self]
--       apply half_pos
--       assumption)
--     refine ⟨min δ₀ δ₁, ?_, ?_⟩
--     · apply lt_min_iff.mpr
--       apply And.intro <;> assumption
--     intro y hy
--     apply spec
--     dsimp
--     show _ + _ < δ
--     dsimp
--     rw [←add_half δ]
--     apply add_lt_add
--     apply spec₀ y
--     · apply IsPseudoMetricSpace.ball_sub _ _ _ _ _ hy
--       apply min_le_left
--     apply spec₁ y
--     · apply IsPseudoMetricSpace.ball_sub _ _ _ _ _ hy
--       apply min_le_right


-- instance (f: ℝ × ℝ -> ℝ) (a: ℝ) [hf: Topology.IsContinuous f]
--   : Topology.IsContinuous (fun x: ℝ => f (a, x)) where
--   isOpen_preimage S Sopen := by
--     intro ε ε_mem
--     have ⟨δ, δ_pos, ball_sub⟩ := hf.isOpen_preimage S Sopen _ ε_mem
--     refine ⟨δ, δ_pos, ?_⟩
--     intro x hx
--     apply ball_sub
--     rw [mem_ball] at *
--     show dist _ _ + dist _ _ < _
--     rwa [dist_self, zero_add]

-- instance (f: ℝ × ℝ -> ℝ) (a: ℝ) [hf: Topology.IsContinuous f]
--   : Topology.IsContinuous (fun x: ℝ => f (x, a)) where
--   isOpen_preimage S Sopen := by
--     intro ε ε_mem
--     have ⟨δ, δ_pos, ball_sub⟩ := hf.isOpen_preimage S Sopen _ ε_mem
--     refine ⟨δ, δ_pos, ?_⟩
--     intro x hx
--     apply ball_sub
--     rw [mem_ball] at *
--     show dist _ _ + dist _ _ < _
--     rwa [dist_self, add_zero]

-- instance instContℝadd₂
--   (f g: ℝ × ℝ -> ℝ) [Topology.IsContinuous f] [Topology.IsContinuous g]
--  : Topology.IsContinuous (fun x: ℝ × ℝ => f x + g x) :=
--   Topology.IsContinuous.comp (fun x => (f x, g x)) (fun x => x.1 + x.2)

-- instance instContℝadd₂'
--   (f g: ℝ -> ℝ) [Topology.IsContinuous f] [Topology.IsContinuous g]
--  : Topology.IsContinuous (fun x: ℝ => f x + g x) := by
--   show Topology.IsContinuous <| (fun x: ℝ × ℝ => x.1 + x.2) ∘ (fun x: ℝ × ℝ => ((fun x => f x.1) x, (fun x => g x.2) x)) ∘ (fun x: ℝ => (x, x))
--   suffices Topology.IsContinuous ((fun x => ((fun x => f x.fst) x, (fun x => g x.snd) x)) ∘ fun x => (x, x)) by
--     apply Topology.IsContinuous.comp
--   suffices Topology.IsContinuous fun x: ℝ×ℝ => ((fun x => f x.fst) x, (fun x => g x.snd) x) by
--     apply Topology.IsContinuous.comp
--   have : Topology.IsContinuous fun x: ℝ×ℝ => f x.fst := Topology.IsContinuous.comp _ _
--   have : Topology.IsContinuous fun x: ℝ×ℝ => g x.snd := Topology.IsContinuous.comp _ _
--   infer_instance

-- instance instContℝmul₂
--   (f g: ℝ × ℝ -> ℝ) [Topology.IsContinuous f] [Topology.IsContinuous g]
--  : Topology.IsContinuous (fun x: ℝ × ℝ => f x * g x) :=
--   Topology.IsContinuous.comp (fun x => (f x, g x)) (fun x => x.1 * x.2)

-- instance instContℝmul₂'
--   (f g: ℝ -> ℝ) [Topology.IsContinuous f] [Topology.IsContinuous g]
--  : Topology.IsContinuous (fun x: ℝ => f x * g x) := by
--   show Topology.IsContinuous <| (fun x: ℝ × ℝ => x.1 * x.2) ∘ (fun x: ℝ × ℝ => ((fun x => f x.1) x, (fun x => g x.2) x)) ∘ (fun x: ℝ => (x, x))
--   suffices Topology.IsContinuous ((fun x => ((fun x => f x.fst) x, (fun x => g x.snd) x)) ∘ fun x => (x, x)) by
--     apply Topology.IsContinuous.comp
--   suffices Topology.IsContinuous fun x: ℝ×ℝ => ((fun x => f x.fst) x, (fun x => g x.snd) x) by
--     apply Topology.IsContinuous.comp
--   have : Topology.IsContinuous fun x: ℝ×ℝ => f x.fst := Topology.IsContinuous.comp _ _
--   have : Topology.IsContinuous fun x: ℝ×ℝ => g x.snd := Topology.IsContinuous.comp _ _
--   infer_instance

-- instance instContℝnpow (n: ℕ) : Topology.IsContinuous (fun x: ℝ => x ^ n) := by
--   induction n with
--   | zero =>
--     conv => { arg 1; intro x; rw [npow_zero] }
--     infer_instance
--   | succ n ih =>
--     conv => { arg 1; intro x; rw [npow_succ] }
--     infer_instance

-- instance instContℝinv? (n: ℤ) : Topology.IsContinuous (fun x: { x: ℝ // x ≠ 0 } => x.val⁻¹? ~(x.property)) where
--   isOpen_preimage := by
--     intro S sopen
--     refine ⟨?_, sorry, ?_⟩
--     exact (S \ {0}).attach.image fun x => x.val⁻¹? ~(x.property)
--     sorry
--     ext x
--     rw [Set.mem_preimage, Set.mem_preimage]


--     sorry

-- instance instContℝzpow (n: ℤ) : Topology.IsContinuous (fun x: { x: ℝ // x ≠ 0 } => x.val ^? n ~(.inl x.property)) := by
--   cases n using Int.coe_cases with
--   | ofNat n =>
--     conv => { arg 1; intro x; rw [zpow?_ofNat] }
--     show Topology.IsContinuous ((fun x: ℝ => x ^ n) ∘ Subtype.val)
--     apply Topology.IsContinuous.comp
--   | negSucc n =>
--     -- conv => { arg 1; intro x; rw [zpow?_negSucc] }
--     sorry

end Real
