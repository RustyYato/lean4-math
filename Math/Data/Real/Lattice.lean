import Math.Order.Lattice.ConditionallyComplete
import Math.Data.Real.Div
import Math.Data.Real.Archimedean
import Math.Data.Int.Lattice

noncomputable section

open Classical Real

instance : Sup ℝ where
  sup := max
instance : Inf ℝ where
  inf := min

instance : NeZero (2: ℝ) where
  out := by
    intro h
    have ⟨k, spec⟩ := Quotient.exact h (1 /? 2) (by decide)
    replace spec := spec _ _ (le_refl _) (le_refl _)
    contradiction

def left_lt_midpoint_of_lt (a b: ℝ) (h: a < b) : a < midpoint a b := by
  unfold midpoint
  rw (occs := [1]) [←add_half a]
  rw [add_div_add₀, div?_eq_mul_inv?, div?_eq_mul_inv?]
  apply Real.mul_lt_mul_of_pos_right
  apply inv?_pos
  exact two_pos
  exact lt_iff_add_lt_add_left.mp h

def midpoint_lt_right_of_lt (a b: ℝ) (h: a < b) : midpoint a b < b := by
  unfold midpoint
  rw (occs := [2]) [←add_half b]
  rw [add_div_add₀, div?_eq_mul_inv?, div?_eq_mul_inv?]
  apply Real.mul_lt_mul_of_pos_right
  apply inv?_pos
  exact two_pos
  exact lt_iff_add_lt_add_right.mp h

def exists_isLUB {S : Set ℝ} (hne : S.Nonempty) (hbdd : S.BoundedAbove) : ∃ x, S.IsLUB x := by
  -- the set of all values which is strictly smaller than *some* value of S
  let L := Set.mk fun a => ∃x ∈ S, a < x
  let R := Lᶜ
  have R_eq_S_ub : R = S.upperBounds := by
    ext x
    apply Iff.intro
    · intro hx y hy
      have := not_exists.mp hx y
      rw [not_and] at this
      rw [←not_lt]
      apply this
      assumption
    · intro hx ⟨y, hy, x_lt_y⟩
      have := not_lt_of_le (hx y hy)
      contradiction
  have l_u_r_eq_univ : L ∪ R = ⊤ := Set.union_compl L
  have l_no_greatest : ∀x, ¬L.IsGreatest x := by
    intro x ⟨⟨a, ha, hx⟩ , h⟩
    have : midpoint x a ∈ L := by
      refine ⟨_, ha, ?_⟩
      apply midpoint_lt_right_of_lt
      assumption
    apply not_lt_of_le <| h (midpoint x a) this
    apply left_lt_midpoint_of_lt
    assumption
  have : ∀l ∈ L, ∀r ∈ R, l < r := by
    intro l ⟨x, hx, hl⟩  r hr
    apply lt_of_lt_of_le
    assumption
    rw [R_eq_S_ub] at hr
    apply hr
    assumption
  suffices ∃x ∈ R, R.IsLeast x by
    obtain ⟨x, hx, rleast⟩ := this
    rw [R_eq_S_ub] at hx
    exists x
    apply And.intro
    apply hx
    intro y hy
    obtain ⟨_, rleast⟩ := rleast
    apply rleast y
    rw [R_eq_S_ub]; assumption
  let L₁: Set ℚ := L.preimage ofRat
  let R₁: Set ℚ := R.preimage ofRat
  have : L₁ ∪ R₁ = ⊤ := by
    apply Set.ext_univ
    intro x
    apply Classical.or_iff_not_imp_left.mpr
    intro h
    apply h
  sorry

-- this is a sequence of rational numbers which
-- is monotonically decreasing and bounded below by the Set S
-- thus it must be a cauchy sequence
def sSup' (S: Set ℝ) : ℕ -> ℚ
| 0 =>
  if h:∃x: ℚ, (x: ℝ) ∈ S.upperBounds then
    Classical.choose h
  else
    0
| n + 1 =>
  if h:∃x: ℚ, (x: ℝ) ∈ S.upperBounds ∧ ∀m, m <= n -> x ≤ sSup' S m then
    Classical.choose h
  else
    sSup' S n

def CauchySeq.sSup (S: Set ℝ) (hS: S.Nonempty) : CauchySeq where
  seq := sSup' S
  is_cacuhy := by
    intro ε εpos
    apply Classical.byContradiction
    intro h
    replace h := fun k => not_exists.mp h k
    conv at h => {
      intro k;
      rw [not_forall]; arg 1; intro a
      rw [not_forall]; arg 1; intro b
      rw [not_imp, not_imp, ]
      dsimp
      rw [not_lt]
    }
    obtain ⟨r, hr⟩ := hS
    let d := ((r - sSup' S 0) /? ε).ceil.natAbs
    have ⟨a, b, ha, hb, εle⟩ := h d



    sorry

def exists_isLUB {S : Set ℝ} (hne : S.Nonempty) (hbdd : S.BoundedAbove) : ∃ x, S.IsLUB x := by
  classical
  obtain ⟨L, hL⟩ := hne
  obtain ⟨U, hU⟩ := hbdd
  let S' (d: ℕ) := (Set.mk fun m: ℤ => ∃ y ∈ S, (m : ℝ) ≤ y * d)
  have : ∀ d : ℕ, Set.BoundedAbove (S' d) := by
    sorry
  let f := fun d => sSup (S' d)
  have hf₁ : ∀n (hn: 0 < n), ∃ y ∈ S, ((f n /? n ~(by
    intro h
    sorry): ℚ) : ℝ) ≤ y := by
    intro n hn
    sorry
  -- have := by
  --   intro S a h ha
  --   simp [sSup]
  --   rw [dif_pos ⟨⟨_, ha⟩, h⟩]
  --   have := Classical.choose_spec (exists_max_of_bounded_above S ⟨_, ha⟩ h)
  --   apply this.right
  --   assumption
  -- cases L, U with | mk L U =>
  -- exists ⟦{
  --   seq n := Rat.binarySearch (fun x => x ∈ S.upperBounds) (L n) (U n) n
  --   is_cacuhy := (by
  --     sorry)
  -- }⟧
  -- apply And.intro
  -- intro x hx



  sorry

instance : SupSet ℝ where
  sSup := sorry

-- this needs exists_isLUB, which requires proving that the reals
-- are an Archemedian set

-- instance : SupSet ℝ where
--   sSup S := if h:S.upperBounds.BoundedBelow then
--     Classical.choose h else 0
-- instance : InfSet ℝ where
--   sInf S := if h:S.lowerBounds.BoundedAbove then Classical.choose h else 0

-- instance : IsConditionallyCompleteLattice ℝ where
--   le_sup_left := le_max_left
--   le_sup_right := le_max_right
--   inf_le_left := min_le_left
--   inf_le_right := min_le_right
--   sup_le := by
--     intro a b k ak bk
--     apply max_le_iff.mpr
--     apply And.intro <;> assumption
--   le_inf := by
--     intro a b k ka kb
--     apply le_min_iff.mpr
--     apply And.intro <;> assumption
--   le_csSup := by
--     intro s a b x
--     simp [sSup]
--     obtain ⟨r, mem_upperbounds⟩ := b
--     have : s.upperBounds.BoundedBelow := by
--       exists a
--       intro b hb
--       apply hb
--       assumption
--     rw [dif_pos this]
--     have this := Classical.choose_spec this
--     rw [Set.mem_lowerBounds] at this

--     sorry
--   csSup_le := sorry
--   le_csInf := sorry
--   csInf_le := sorry

end
