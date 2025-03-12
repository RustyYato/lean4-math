import Math.Data.Nat.Sqrt

namespace Nat

/-- returns the largest number `n` such at `n * (n + 1) / 2 ≤ a` --/
def inv_triangle (a: Nat) : Nat :=
  (sqrt (8 * a + 1) - 1) / 2

/-- the nth triangle number --/
def triangle (n: Nat) := n * (n + 1) / 2

def triangle_zero : triangle 0 = 0 := rfl
def triangle_succ (n: Nat) : triangle (n + 1) = triangle n + (n + 1) := by
  unfold triangle
  apply Nat.mul_left_cancel (n := 2) (by decide)
  rw [Nat.mul_add 2, Nat.mul_div_cancel', Nat.mul_div_cancel']
  any_goals apply two_dvd_mul_succ
  simp [Nat.mul_add, Nat.add_mul]
  omega

def inv_triangle_helper : 8 * (triangle n) + 1 = (2 * n + 1) * (2 * n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [triangle_succ, Nat.add_comm n.triangle, Nat.mul_add,
      Nat.add_assoc, ih]
    simp [Nat.add_mul, Nat.mul_add]
    omega

def triangle_left_inv: Function.IsLeftInverse inv_triangle triangle := by
  intro n
  unfold inv_triangle
  rw [inv_triangle_helper, sqrt_sq, Nat.add_sub_cancel, Nat.mul_div_cancel_left]
  decide

def sqrt_sq_add (n: Nat) : ∃m, n = n.sqrt * n.sqrt + m ∧ m ≤ 2 * n.sqrt := by
  have := sqrt_sq_le_self n
  rw [Nat.le_iff_exists_sum] at this
  obtain ⟨m, eq⟩ := this
  exists m
  apply And.intro eq
  apply Nat.le_of_lt_succ
  show m < 2 * _ + 1
  apply Nat.lt_of_add_lt_add_left
  rw [←eq, Nat.add_succ]
  apply Nat.lt_succ_of_le
  rw [Nat.two_mul, ←Nat.add_assoc]
  apply sqrt_le_add

def sq_add_le_sq_succ {n k: Nat} :
  k < 4 * n + 4 ↔ n * n + k < (n + 2) * (n + 2) := by
  apply Iff.intro
  intro h
  simp [Nat.mul_add, Nat.add_mul]
  omega
  intro h
  simp [Nat.mul_add, Nat.add_mul] at h
  rw [Nat.add_assoc] at h
  replace h := Nat.lt_of_add_lt_add_left h
  omega

-- def inv_triangle_add (h: k ≤ n) : inv_triangle (triangle n + k) = n := by
--   unfold inv_triangle
--   rw [Nat.add_comm _ k, Nat.mul_add, Nat.add_assoc, Nat.add_comm, inv_triangle_helper]
--   rw [Nat.div_eq_iff]
--   apply And.intro
--   rw [←Nat.pred_eq_sub_one, Nat.pred_le_iff_le_succ, Nat.succ_eq_add_one]
--   rw [←Nat.lt_succ, sqrt_lt_iff]
--   rw [Nat.sub_add_cancel, Nat.mul_comm _ 2]
--   show _ < (2 * n + 3) * (2 * n + 3)
--   apply sq_add_le_sq_succ.mp
--   rw [Nat.mul_add]
--   apply Nat.lt_of_succ_le
--   apply Nat.succ_le_succ
--   rw [←Nat.mul_assoc]
--   apply Nat.le_trans
--   apply Nat.mul_le_mul_left
--   assumption
--   apply Nat.le_add_right
--   apply Nat.succ_le_succ
--   apply Nat.zero_le
--   rw [Nat.sub_one]
--   apply Nat.le_pred_of_lt
--   -- apply Nat.lt_sqrt
--   sorry






--   -- rw [sqrt_add_eq, Nat.add_sub_cancel, Nat.mul_div_cancel_left]
--   -- decide

--   -- have ⟨i, k_eq, i_le⟩ := sqrt_sq_add k
--   -- rw [k_eq]



--   sorry

def triangle_strict_monotone (a b: Nat) : a < b -> triangle a < triangle b := by
  intro lt
  induction b generalizing a with
  | zero => contradiction
  | succ b ih =>
    rw [triangle_succ]
    cases a with
    | zero => apply Nat.zero_lt_succ
    | succ a =>
      rw [triangle_succ]
      apply Nat.add_lt_add
      apply ih
      apply Nat.lt_of_succ_lt_succ
      assumption
      assumption

def triangle_inj : Function.Injective triangle := triangle_left_inv.Injective

def pair (a b: Nat) :=
  triangle (a + b) + a

def unpair (x: Nat): Nat × Nat :=
  let ab := inv_triangle x
  let a := x - triangle ab
  let b := ab - a
  ⟨a, b⟩

def unpair_pair (x: Nat) : pair (unpair x).1 (unpair x).2 = x := sorry

def unpair_pair.helper₀ (a b: Nat) (h: b ≤ a) :
  (a - b) * (a - b) + 2 * a * b = a * a + b * b := by
  apply Int.ofNat.inj
  rw [Nat.two_mul, Int.ofNat_eq_coe, Int.ofNat_eq_coe]
  simp [Int.ofNat_sub h, Int.sub_mul, Int.mul_sub]
  simp [Int.sub_eq_add_neg, Int.mul_comm b, Int.neg_add, Int.add_mul]
  omega

-- def sub_mul (a b k: Nat) : (a - b) * k = a * k - b * k := by
--   by_cases h:b < a
--   · apply Int.ofNat.inj
--     simp
--     repeat rw [Int.ofNat_sub]
--     repeat rw [Int.ofNat_mul]
--     rw [Int.sub_mul]
--     apply Nat.mul_le_mul_right
--     apply Nat.le_of_lt
--     assumption
--     apply Nat.le_of_lt
--     assumption
--   · replace h := Nat.le_of_not_lt h
--     rw [Nat.sub_eq_zero_iff_le.mpr h, Nat.sub_eq_zero_iff_le.mpr, Nat.zero_mul]
--     apply Nat.mul_le_mul_right
--     assumption
-- def mul_sub (a b k: Nat) : k * (a - b) = k * a - k * b := by
--   iterate 3 rw [Nat.mul_comm k]
--   rw [sub_mul]

-- def div_add_div_le (a b k: Nat) : a / k + b / k ≤ (a + b) / k := by
--   cases k
--   iterate 3 rw [Nat.div_zero]
--   apply Nat.le_refl
--   rename_i k
--   rw [Nat.le_div_iff_mul_le (Nat.zero_lt_succ _)]
--   rw [Nat.add_mul]
--   apply Nat.add_le_add
--   apply Nat.div_mul_le_self
--   apply Nat.div_mul_le_self

-- def pair_unpair (a b: Nat) : unpair (pair a b) = ⟨a, b⟩ := by
--   unfold pair unpair
--   dsimp
--   rw [inv_triangle_add, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
--   apply Nat.le_add_right
  -- generalize hw:a + b = w
  -- generalize ht:(w * (w + 1)) / 2 = t
  -- generalize hz:t + a = z
  -- have : 2 ∣ w * (w + 1) := two_dvd_mul_succ w
  -- have sqrt_eq : (8 * t + 1).sqrt = 2 * w + 1 := by
  --   subst t
  --   show (4 * 2 * _ + _).sqrt = _
  --   rw [Nat.mul_assoc, Nat.mul_div_cancel' this]
  --   rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
  --   apply sqrt_eq_of_sq_eq
  --   simp [Nat.mul_add, Nat.add_mul]
  --   rw [←Nat.add_assoc, Nat.add_assoc (_ * _)]
  --   congr 2
  --   ac_rfl
  --   rw [←Nat.two_mul, ←Nat.mul_assoc]
  -- unfold unpair
  -- dsimp
  -- suffices ((8 * z + 1).sqrt - 1) / 2 = w by
  --   rw [this]; clear this
  --   subst z; subst t; subst w
  --   congr
  --   rw [Nat.add_sub_cancel_left]
  --   omega
  -- apply Nat.eq_of_le_of_lt_succ
  -- · apply (Nat.le_div_iff_mul_le (by decide)).mpr
  --   apply Nat.le_pred_of_lt
  --   apply Nat.lt_of_succ_le
  --   show w * 2 + 1 ≤ _
  --   apply (Nat.le_sqrt_iff _).mpr
  --   rw [square_add, Nat.mul_one, Nat.mul_one]
  --   apply Nat.succ_le_succ
  --   have : w * 2 * (w * 2) + 2 * (w * 2)
  --     = 2 * 2 * (w * w) + 2 * 2 * (w * 1) := by ac_rfl
  --   rw [this]; clear this
  --   rw [←Nat.mul_add, ←Nat.mul_add]
  --   show _ ≤ 4 * 2 * _
  --   rw [Nat.mul_assoc 4]
  --   apply Nat.mul_le_mul_left
  --   subst z
  --   subst t
  --   rw [Nat.mul_add 2, Nat.mul_div_cancel']
  --   apply Nat.le_add_right
  --   assumption
  -- · rw [Nat.div_lt_iff_lt_mul (by decide), ←Nat.add_lt_add_iff_right (k := 1), Nat.sub_add_cancel]
  --   rw [Nat.add_mul, Nat.add_assoc]
  --   show _ < _ + 3
  --   rw [Nat.sqrt_lt_iff, Nat.mul_comm _ 2, square_add, Nat.mul_comm _ 3]
  --   apply Nat.succ_lt_succ
  --   have : 2 * w * (2 * w) + 3 * (2 * (2 * w)) + 8
  --        = 2 * 2 * (w * w) + 2 * 2 * (3 * w) + 8 := by ac_rfl
  --   rw [this]; clear this; show 4 * 2 * _ < _ + 4 * 2
  --   rw [←Nat.mul_add, ←Nat.mul_add, Nat.mul_assoc]
  --   rw [Nat.mul_lt_mul_left (by decide)]
  --   show _ < _ + (1 + 2) * _ + 2 * 1
  --   rw [Nat.add_mul, Nat.mul_comm 1, ←Nat.add_assoc, ←Nat.mul_add,
  --     Nat.add_assoc, ←Nat.mul_add]
  --   subst z; subst t
  --   rw [Nat.mul_add, Nat.mul_div_cancel' (by assumption)]
  --   apply Nat.add_lt_add_left
  --   rw [Nat.mul_lt_mul_left (by decide), Nat.lt_succ]
  --   subst w; apply Nat.le_add_right
  --   apply Nat.succ_le_of_lt
  --   apply sqrt_pos
  --   apply Nat.zero_lt_succ

-- def pair_inj : Function.Injective₂ pair := by
--   intro a b c d eq
--   have : unpair (a.pair b) = unpair (c.pair d) := by rw [eq]
--   rw [pair_unpair, pair_unpair] at this
--   exact Prod.mk.inj this

-- def div_lt_div (a b k: Nat) : 0 < k -> a + (k - 1) < b -> a / k < b / k := by
--   intro kpos altb
--   rw [Nat.lt_div_iff_mul_lt]
--   apply Nat.lt_of_le_of_lt
--   apply Nat.div_mul_le_self
--   apply Nat.lt_sub_of_add_lt
--   assumption
--   assumption

-- -- def unpair_inj : Function.Injective unpair := by
-- --   suffices ∀{a b: Nat}, a < b -> unpair a ≠ unpair b by
-- --     intro a b eq
-- --     apply Decidable.byContradiction
-- --     intro h
-- --     rcases Nat.lt_or_gt_of_ne h with ab | ba
-- --     exact this ab eq
-- --     exact this ba eq.symm
-- --   intro a b a_lt_b
-- --   induction b generalizing a with
-- --   | zero => contradiction
-- --   | succ b ih =>
-- --     cases a with
-- --     | zero =>
-- --       intro h
-- --       sorry
-- --     | succ a =>
-- --       replace a_lt_b := Nat.lt_of_succ_lt_succ a_lt_b



-- --   -- unfold unpair
-- --   -- generalize ha₀:((8 * a + 1).sqrt - 1) / 2 = a₀
-- --   -- generalize hb₀:((8 * b + 1).sqrt - 1) / 2 = b₀
-- --   -- dsimp
-- --   -- intro h
-- --   -- have : ∀{a}, 1 ≤ (8 * a + 1).sqrt := by
-- --   --   intro a
-- --   --   apply Nat.succ_le_of_lt
-- --   --   apply Nat.sqrt_pos
-- --   --   apply Nat.zero_lt_succ
-- --   -- have ⟨h₀, h₁⟩ := Prod.mk.inj h; clear h






-- --   sorry

-- -- def unpair_pair' (z: Nat) : pair (unpair z).1 (unpair z).2 = z := by
-- --   apply unpair_inj
-- --   exact pair_unpair _ _

-- def unpair_pair (z: Nat) : pair (unpair z).1 (unpair z).2 = z := by
--   generalize h:z.unpair=a'
--   obtain ⟨a, b⟩ := a'
--   dsimp
--   unfold pair
--   unfold unpair at h
--   dsimp at h
--   have ⟨ha, hb⟩ := Prod.mk.inj h; clear h
--   generalize hw:((8 * z + 1).sqrt - 1) / 2 = w
--   rw [hw] at ha hb
--   subst a; subst b
--   have le_z : w * (w + 1) / 2 ≤ z := by
--     rw [Nat.mul_add, Nat.mul_one, Nat.div_le_iff_le_mul (by decide)]
--     show _ ≤ _ + 1
--     subst w
--     apply Nat.le_trans
--     apply Nat.add_le_add_right
--     apply Nat.div_mul_le_mul_div
--     conv => {
--       lhs; rhs; lhs
--       rw [←Nat.mul_div_cancel (_ - _) (n := 2) (by decide)]
--     }
--     rw [Nat.div_div_eq_div_mul]
--     apply Nat.le_trans
--     apply Nat.div_add_div_le
--     rw [Nat.div_le_iff_le_mul]
--     conv => {
--       lhs; rhs
--       rw [Nat.mul_comm, ←Nat.mul_one (sqrt _)]
--     }
--     rw [mul_sub (k := 2), ←Nat.add_sub_assoc, ←Nat.mul_assoc, unpair_pair.helper₀]
--     simp
--     erw [Nat.pred_le_iff_le_succ]
--     show _ * _ ≤ _ + 4
--     apply Nat.le_trans
--     apply sqrt_sq_le_self
--     rw [Nat.add_mul, Nat.add_assoc, Nat.mul_assoc, Nat.mul_comm z]
--     apply Nat.add_le_add_left
--     decide
--     apply Nat.succ_le_of_lt
--     apply sqrt_pos
--     apply Nat.zero_lt_succ
--     apply Nat.mul_le_mul_left
--     apply Nat.succ_le_of_lt
--     rw [Nat.mul_one]
--     apply sqrt_pos
--     apply Nat.zero_lt_succ
--     decide
--   have le_w : z - (w * (w + 1)) / 2 ≤ w := by
--     clear le_z
--     apply Nat.le_of_mul_le_mul_left (c := 2) _ (by decide)
--     rw [Nat.mul_sub, Nat.mul_div_cancel']
--     rw [Nat.sub_le_iff_le_add, Nat.mul_add, Nat.mul_one]
--     rw [Nat.add_comm, Nat.add_assoc]
--     have : w + 2 * w = 3 * w := by
--       conv => { lhs; lhs; rw [←Nat.one_mul w] }
--       rw [←Nat.add_mul]
--     rw [this]; clear this; subst w
--     apply Nat.le_of_mul_le_mul_left (c := 4) _ (by decide)
--     rw [Nat.mul_add]
--     show _ ≤ 2 * 2 * _ + 2 * 2 * _
--     rw [Nat.mul_assoc 2, ←Nat.mul_assoc 2 (_ / 2), Nat.mul_comm 2 (_ * _), Nat.mul_assoc,
--       Nat.mul_comm _ 2, Nat.mul_assoc 2 2  (3 * _), Nat.mul_left_comm 2 3]
--     rw [Nat.mul_div_self_eq_mod_sub_self, ←Nat.mul_assoc 2 3]
--     generalize hn:(8 * z + 1).sqrt - 1 = n
--     have sqrt_eq : (8 * z + 1).sqrt = n + 1 := by
--       rw [←hn, Nat.sub_add_cancel]
--       apply Nat.succ_le_of_lt
--       apply sqrt_pos
--       apply Nat.zero_lt_succ
--     have := sqrt_sq_le_self (8 * z + 1)
--     rw [sqrt_eq] at this
--     repeat sorry
--   apply Int.ofNat_inj.mp
--   simp [Int.ofNat_sub le_z, Int.ofNat_sub le_w]

--   sorry

end Nat
