import Math.Data.Poly.Degree
import Math.Data.FinSupp.Fintype
import Math.Algebra.Dvd
import Math.Order.TopBot.Linear

def Nat.sub_sub' (a b c: Nat) (h: c ≤ b) : a - (b - c) = a + c - b := by omega

namespace Poly

variable [SemiringOps P] [IsSemiring P]

instance : Dvd P[X] where
  dvd a b := ∃k, b = a * k

instance : IsLawfulDvd P[X] where

end Poly

namespace Poly

variable [RingOps P] [IsRing P] [IsCommMagma P] [DecidableEq P] [IsNontrivial P]

def deg_nontrivial_of_invertible (b: P[X]) (h: IsInvertible b.lead) : ⊥ < b.degree := by
  unfold lead degreeNat at h
  split at h
  rename_i h'
  rw [h']
  apply WithBot.LT.bot
  rename_i h'
  cases degree_eq_bot_iff_eq_zero.mp h'
  have : ∀x, AddMonoidAlgebra.toFinsupp (0: P[X]) x = 0 := fun _ => rfl
  rw [this] at h
  have := h.invOf_mul
  rw [mul_zero] at this
  have := zero_ne_one _ this
  contradiction

def divmod_sub_coeff (a b : P[X]) (h: IsInvertible (b.lead)) : P[X] :=
  let x := (a.toFinsupp a.degreeNat) * ⅟(b.lead)
  a - x • b * X^(a.degreeNat - b.degreeNat)

def divmod_rec_lemma [IsNontrivial P] [IsCommMagma P] (a b: P[X]) (h: IsInvertible (b.lead)) (h₀: b.degree ≤ a.degree): (divmod_sub_coeff a b h).degree < a.degree := by
  let a' := a - (a.toFinsupp a.degreeNat * ⅟(b.lead)) • b * X ^ (a.degreeNat - b.degreeNat)
  show a'.degree < _
  have bdeg_nontrivial : ⊥ < b.degree := deg_nontrivial_of_invertible b h
  have adeg_nontrivial : ⊥ < a.degree := by
    apply lt_of_lt_of_le bdeg_nontrivial
    assumption
  cases hd:a.degree with
  | bot =>
    rw [hd] at adeg_nontrivial
    contradiction
  | of deg =>
    have bdeg_eq_degNat : b.degree = b.degreeNat := by
      unfold degreeNat
      split; assumption
      rename_i g
      replace g : b.degree = ⊥ := g
      cases degree_eq_bot_iff_eq_zero.mp g
      rw [lead_zero] at h
      have := h.invOf_mul
      rw [mul_zero] at this
      contradiction
    have adegnat : a.degreeNat = deg := by
      rw [degree_eq_degreeNat] at hd
      cases hd; rfl
      exact adeg_nontrivial
    apply degree_lt
    intro i hi
    rw [bdeg_eq_degNat, a.degree_eq_degreeNat adeg_nontrivial] at h₀
    cases h₀; rename_i h₁
    rcases lt_or_eq_of_le hi with hi | rfl
    · unfold a'
      rw [sub_eq_add_neg]
      show a.toFinsupp i + AddMonoidAlgebra.toFinsupp (-_) i = _
      rw [neg_mul_left, ←neg_smul', coeff_mul_Xpow, Nat.sub_sub', Nat.add_comm i,
        Nat.add_sub_assoc]
      show _ + _ * -(b.toFinsupp (b.degreeNat + (i - a.degreeNat))) = 0
      unfold lead
      rw (occs := [2]) [b.of_degree_lt]
      rw [neg_zero, mul_zero]
      rw [a.of_degree_lt _ (hd ▸ (WithBot.LT.of hi)), zero_add]
      rw [bdeg_eq_degNat]
      apply WithBot.LT.of
      simp; omega
      apply le_of_lt
      rw [adegnat]
      assumption
      assumption
      omega
    · unfold a'
      rw [sub_eq_add_neg]
      show a.toFinsupp deg + AddMonoidAlgebra.toFinsupp (-_) deg = _
      rw [neg_mul_left, ←neg_smul', coeff_mul_Xpow, Nat.sub_sub', Nat.add_comm deg,
        Nat.add_sub_assoc]
      show _ + _ * -(b.toFinsupp (b.degreeNat + (deg - a.degreeNat))) = 0
      rw [adegnat, Nat.sub_self, add_zero, ←neg_mul_right,
        mul_assoc]
      erw [h.invOf_mul, mul_one, add_neg_cancel]
      rw [adegnat]
      · assumption
      · omega

def divmod [IsNontrivial P] [IsCommMagma P] (a b: P[X]) (h: IsInvertible (b.lead)) : P[X] × P[X] :=
  if a.degree >= b.degree then
    let x := (a.toFinsupp a.degreeNat) * ⅟(b.lead)
    let z := a - x • b * X^(a.degreeNat - b.degreeNat)
    let (d, m) := divmod z b h
    (d + C x * X ^ (a.degreeNat - b.degreeNat), m)
  else
    (0, a)
termination_by a.degree
decreasing_by
  apply divmod_rec_lemma
  assumption

def divmod_of_lt (a b: P[X]) {inv: IsInvertible (b.lead)} (h: a.degree < b.degree) : a.divmod b inv = (0, a) := by
  unfold divmod
  rw [if_neg]
  apply not_le_of_lt
  assumption
def divmod_of_le (a b: P[X]) {inv: IsInvertible (b.lead)} (h: b.degree ≤ a.degree) :
  a.divmod b inv =
    let x := (a.toFinsupp a.degreeNat) * ⅟(b.lead)
    let z := a - x • b * X^(a.degreeNat - b.degreeNat)
    let (d, m) := divmod z b inv
    (d + C x * X ^ (a.degreeNat - b.degreeNat), m) := by
    rw [divmod]
    rw [if_pos h]

def div (a b: P[X]) [inv: IsInvertible (b.lead)] : P[X] := (divmod a b inv).1
def mod (a b: P[X]) [inv: IsInvertible (b.lead)] : P[X] := (divmod a b inv).2

def divmod_eq_div_pair_mod (a b: P[X]) [inv: IsInvertible (b.lead)] :
  divmod a b inv = (div a b, mod a b) := rfl

def div_of_lt (a b: P[X]) {inv: IsInvertible (b.lead)} (h: a.degree < b.degree) : a.div b = 0 := by
  have := divmod_of_lt a b (inv := inv) h
  rw [divmod_eq_div_pair_mod] at this
  exact (Prod.mk.inj this).left
def div_of_le (a b: P[X]) {inv: IsInvertible (b.lead)} (h: b.degree ≤ a.degree) :
  a.div b =
    let x := (a.toFinsupp a.degreeNat) * ⅟(b.lead)
    let z := divmod_sub_coeff a b inferInstance
    div z b + C x * X ^ (a.degreeNat - b.degreeNat) := by
    have := divmod_of_le a b (inv := inv) h
    rw [divmod_eq_div_pair_mod] at this
    exact (Prod.mk.inj this).left

def mod_of_lt (a b: P[X]) {inv: IsInvertible (b.lead)} (h: a.degree < b.degree) : a.mod b = a := by
  have := divmod_of_lt a b (inv := inv) h
  rw [divmod_eq_div_pair_mod] at this
  exact (Prod.mk.inj this).right
def mod_of_le (a b: P[X]) {inv: IsInvertible (b.lead)} (h: b.degree ≤ a.degree) :
  a.mod b = mod (divmod_sub_coeff a b inferInstance) b := by
    have := divmod_of_le a b (inv := inv) h
    rw [divmod_eq_div_pair_mod] at this
    exact (Prod.mk.inj this).right

variable (a b: P[X]) (inv: IsInvertible (b.lead))

instance : @Relation.IsWellFounded (WithBot Nat) (· < ·) := inferInstance

def divmod_induction {motive: P[X] -> Prop}
  (deg_lt: ∀a: P[X], a.degree < b.degree -> motive a)
  (le_deg: ∀a: P[X], b.degree ≤ a.degree -> motive (divmod_sub_coeff a b inferInstance) -> motive a):
  ∀a, motive a := by
  intro a
  induction h:a.degree using Relation.wfInduction (α := WithBot Nat) (· < ·) generalizing a b with
  | h deg ih =>
  rcases lt_or_le a.degree b.degree with h | h
  apply deg_lt
  assumption
  apply le_deg
  assumption
  subst deg
  apply ih (divmod_sub_coeff a b inferInstance).degree
  apply divmod_rec_lemma
  assumption
  assumption
  assumption
  rfl

def div_mul_add_mod : div a b * b + mod a b = a := by
  induction a using divmod_induction b inferInstance with
  | deg_lt a h => rw [div_of_lt, mod_of_lt]; simp; repeat assumption
  | le_deg a h ih =>
    rw [div_of_le, mod_of_le]
    simp
    rw [add_mul, add_comm_right, ih]
    unfold divmod_sub_coeff
    simp
    rw [mul_comm_right, ←smul_eq_const_mul, sub_add_cancel]
    assumption
    assumption

def mod_degree_lt : (mod a b).degree < b.degree := by
  induction a using divmod_induction b inferInstance with
  | deg_lt a h =>
    rw [mod_of_lt _ _ h]
    assumption
  | le_deg a h ih =>
    rw [mod_of_le _ _ h]
    apply ih

def eq_zero_of_dvd_of_degree_lt [NoZeroDivisors P] (a b: P[X]) (h: a ∣ b) (g: b.degree < a.degree) : b = 0 := by
  obtain ⟨k, rfl⟩ := h
  cases ha:a.degree with
  | bot => simp [degree_eq_bot_iff_eq_zero.mp ha]
  | of deg =>
  cases hk:k.degree with
  | bot => simp [degree_eq_bot_iff_eq_zero.mp hk]
  | of kdeg =>
    rw [ha] at g
    rw [Poly.mul_degree] at g
    rw [ha, hk] at g
    cases g; rename_i g
    have := Nat.not_le_of_lt g (Nat.le_add_right _ _)
    contradiction

variable {p: P[X]} {inv: IsInvertible p.lead} [NoZeroDivisors P]

def mod_mod (a: P[X]) : (a.mod p).mod p = a.mod p := by
  rw [mod_of_lt (a.mod p)]
  apply mod_degree_lt

def mod_eq_iff_sub_dvd (a b: P[X]) : p ∣ (a - b) ↔ a.mod p = b.mod p := by
  apply Iff.intro
  · intro eq
    rw [←div_mul_add_mod a p inferInstance, ←div_mul_add_mod b p inferInstance] at eq
    replace eq : p ∣ _ := eq
    rw [sub_eq_add_neg, neg_add_rev, ←add_assoc, add_assoc (_ * _),
      add_comm_right, ←sub_eq_add_neg, ←sub_eq_add_neg, ←sub_mul] at eq
    replace eq := dvd_add eq (dvd_mul_right p (b.div p - a.div p))
    rw [add_comm_right, ←neg_sub, ←neg_mul_left, neg_add_cancel,
      zero_add] at eq
    have := Poly.eq_zero_of_dvd_of_degree_lt _ _ eq ?_
    apply eq_of_sub_eq_zero
    assumption
    rw [sub_eq_add_neg]
    apply lt_of_le_of_lt
    apply Poly.add_degree
    rw [Poly.neg_degree]
    apply max_lt_iff.mpr
    apply And.intro
    apply mod_degree_lt
    apply mod_degree_lt
  · intro eq
    rw [←a.div_mul_add_mod p inv, ←b.div_mul_add_mod p inv, eq]
    clear eq
    rw [sub_add, add_sub_cancel', ←sub_mul]
    apply dvd_mul_right

def divmod_sub_coeff_degree_le_self (a: P[X]) (h: p.degree ≤ a.degree) : (a.divmod_sub_coeff p inferInstance).degree ≤ a.degree := by
  unfold divmod_sub_coeff
  simp
  apply le_trans
  apply sub_degree
  apply max_le_iff.mpr
  apply And.intro (le_refl _)
  rw [smul_def, mul_assoc, mul_degree, mul_degree]
  rw [Xpow_degree]
  have := deg_nontrivial_of_invertible _ inv
  rw [p.degree_eq_degreeNat this]
  rw [degree_add, Nat.add_sub_cancel']
  show degree_add (C _).degree _ ≤ _
  rw [const_degree_eq, a.degree_eq_degreeNat]
  split
  apply bot_le
  apply WithBot.LE.of
  rw [Nat.zero_add]
  apply lt_of_lt_of_le this
  assumption
  have := h
  rw [p.degree_eq_degreeNat, a.degree_eq_degreeNat] at this
  cases this; assumption
  clear this
  apply lt_of_lt_of_le this
  assumption
  assumption

def mod_degree_le_self (a: P[X]) : (a.mod p).degree ≤ a.degree := by
  induction a using divmod_induction p inv with
  | deg_lt a h => rw [mod_of_lt _ _ h]
  | le_deg a h ih =>
    rw [mod_of_le _ _ h]
    apply le_trans ih
    apply divmod_sub_coeff_degree_le_self
    assumption

def div_degree_le_self (a: P[X]) : (a.div p).degree ≤ a.degree := by
  induction a using divmod_induction p inv with
  | deg_lt a h => rw [div_of_lt _ _ h]; apply bot_le
  | le_deg a h ih =>
    rw [div_of_le _ _ h]
    simp
    apply le_trans
    apply add_degree
    apply max_le_iff.mpr
    apply And.intro
    apply le_trans ih
    apply divmod_sub_coeff_degree_le_self
    assumption
    rw [mul_degree, const_degree_eq, Xpow_degree]
    split
    apply bot_le
    rw [a.degree_eq_degreeNat]
    apply WithBot.LE.of
    omega
    apply lt_of_lt_of_le _ h
    exact deg_nontrivial_of_invertible p inv

def mul_add_mod (a b: P[X]) (hb: b.degree < p.degree) : (a * p + b).mod p = b := by
  rw (occs := [2]) [←mod_of_lt _ _ hb]
  apply (mod_eq_iff_sub_dvd _ _).mp
  rw [add_sub_cancel']
  apply dvd_mul_right

def zero_mod : mod 0 p = 0 := by
  suffices (mod 0 p).degree = ⊥ by
    rw [degree_eq_bot_iff_eq_zero.mp this]
  apply le_antisymm
  exact mod_degree_le_self 0 (inv := inv)
  apply bot_le

def zero_div : div 0 p = 0 := by
  suffices (div 0 p).degree = ⊥ by
    rw [degree_eq_bot_iff_eq_zero.mp this]
  apply le_antisymm
  exact div_degree_le_self 0 (inv := inv)
  apply bot_le

def mul_mod_right (a: P[X]) : (a * p).mod p = 0 := by
  rw [←zero_mod]
  apply (mod_eq_iff_sub_dvd _ _).mp
  rw [sub_zero]
  apply dvd_mul_right

def mul_mod_left (a: P[X]) : (p * a).mod p = 0 := by
  rw [←zero_mod]
  apply (mod_eq_iff_sub_dvd _ _).mp
  rw [sub_zero]
  apply dvd_mul_left

def divmod_sub_coeff' (a q r: P[X]) (hr: r.degree < p.degree) :
  (q * p + r).divmod_sub_coeff p inv = sorry /-q.divmod_sub_coeff p inv + r-/ := by
  unfold divmod_sub_coeff
  simp
  conv => {
    lhs
    rw (occs := [1]) [add_comm]
    rw [add_sub_assoc, smul_def, mul_comm_right, ←smul_def, ←sub_mul, add_comm]

  }
  sorry

def div_mod_unique (a q r: P[X]) (hr: r.degree < p.degree) : a = q * p + r -> q = a.div p ∧ r = a.mod p := by
  classical
  intro eq
  have hp : p.degree = p.degreeNat := by
    rw [p.degree_eq_degreeNat]
    exact deg_nontrivial_of_invertible p inv
  induction a using divmod_induction p inv generalizing q r with
  | deg_lt a ha =>
    subst a
    rw [div_of_lt _ _ ha, mod_of_lt _ _ ha]
    suffices q = 0 by simp [this]
    cases hq:q.degree
    rw [degree_eq_bot_iff_eq_zero.mp hq]
    rw [add_degree_of_ne_degree, mul_degree, hp] at ha
    rw [hq] at ha
    replace ha := (max_lt_iff.mp ha).left
    cases ha; rename_i ha
    have := Nat.not_le_of_lt ha  (Nat.le_add_left _ _)
    contradiction
    rw [mul_degree]
    symm; apply ne_of_lt
    rw [hq, p.degree_eq_degreeNat]
    cases hr':r.degree
    apply WithBot.LT.bot
    apply WithBot.LT.of
    rw [hr', hp] at hr
    cases hr
    omega
    rw [hp]; apply WithBot.LT.bot
  | le_deg a ha ih =>
    rw [div_of_le _ _ ha, mod_of_le _ _ ha]
    simp
    subst a


    sorry

def mul_div_cancel_right (a: P[X]) : (a * p).div p = a := by
  sorry

def mul_add_div (a b: P[X]) (hb: b.degree < p.degree) : (a * p + b).div p = a := by
  have := div_mul_add_mod (a * p + b) p inv
  rw [mul_add_mod a b hb (p := p) (inv := inv)] at this
  replace := add_right_cancel this
  have h := mul_div_cancel_right a (p := p) (inv := inv)
  rw [←this] at h
  rw [mul_div_cancel_right] at h
  assumption

-- def divmod_sub_coeff_of_lt_of_le (a b: P[X]) (ha: a.degree < p.degree) (hb: p.degree ≤ b.degree) : (a + b).divmod_sub_coeff p inv = a + b.divmod_sub_coeff p inv := by
--   unfold divmod_sub_coeff
--   simp
--   rw [add_sub_assoc]
--   congr 3
--   · show ((a.toFinsupp (a + b).degreeNat + b.toFinsupp (a + b).degreeNat) * ⅟(p.toFinsupp p.degreeNat)) • p =
--         (b.lead * ⅟(p.toFinsupp p.degreeNat)) • p
--     rw [of_degree_lt, zero_add]
--     congr 3
--     apply WithBot.of_inj.mp
--     rw [←degree_eq_degreeNat, ←degree_eq_degreeNat]
--     apply le_antisymm
--     apply degree_is_minimal
--     intro i h
--     show a.toFinsupp i + b.toFinsupp i = 0
--     rw [of_degree_lt, of_degree_lt, add_zero]
--     assumption
--     apply lt_trans ha
--     apply lt_of_le_of_lt hb
--     assumption
--     have := add_degree a b
--     apply degree_is_minimal
--     intro i h
--     rw [of_degree_lt]


--     repeat sorry
--   · sorry

-- def const_mul_add_div (a: P) (b: P[X]) : (C a * p + b).div p = C a + b.div p := by

--   sorry

-- def add_div (a b: P[X]) : (a + b).div p = a.div p + b.div p := by
--   induction a using divmod_induction p inv generalizing b with
--   | deg_lt a ha =>
--     rw [div_of_lt _ _ ha, zero_add]
--     induction b using divmod_induction p inv with
--     | deg_lt b hb =>
--       rw [div_of_lt _ _ hb, div_of_lt]
--       apply lt_of_le_of_lt
--       apply Poly.add_degree
--       apply max_lt_iff.mpr
--       apply And.intro
--       assumption
--       assumption
--     | le_deg b hb ih =>
--       rw [div_of_le]
--       simp

--       sorry
--   | le_deg => sorry

-- def add_mod (a b: P[X]) : (a + b).mod p = a.mod p + b.mod p := by
--   have ha := div_mul_add_mod a p inv
--   have hb := div_mul_add_mod b p inv
--   have h := div_mul_add_mod (a + b) p inv
--   conv at h => { rhs; rw [←ha, ←hb] }
--   sorry

-- def mul_add_div (a b: P[X]) : (a * p + b).div p = a + b.div p := by
--   have := div_mul_add_mod (a * p + b) p inv

--   sorry

-- --   induction b using Poly.divmod_induction p inv generalizing a with
-- --   | deg_lt b hb =>
-- --     rw [div_of_lt _ _ hb, add_zero]
-- --     induction a using Poly.divmod_induction p inv with
-- --     | deg_lt a ha =>
-- --       by_cases h:a=0
-- --       subst a; simp; rw [div_of_lt _ _ hb]
-- --       rw [div_of_le]
-- --       simp

-- --       sorry
-- --     | le_deg a ha ih => sorry
-- --   | le_deg b h ih =>
-- --     rw [mod_of_le _ _ h, mod_of_le]
-- --     rw [divmod_sub_coeff]
-- --     rw [smul_def, mul_comm_right, ←smul_def, add_comm,
-- --       add_sub_assoc, ←sub_mul, add_comm]

-- --     sorry

-- -- def mul_add_mod (a b: P[X]) : (a * p + b).mod p = b.mod p := by
-- --   have := div_mul_add_mod (a * p + b) p inv
-- --   induction b using Poly.divmod_induction p inv generalizing a with
-- --   | deg_lt b h =>
-- --     rw [mod_of_lt _ _ h]
-- --     sorry
-- --   | le_deg b h ih =>
-- --     rw [mod_of_le _ _ h, mod_of_le]
-- --     rw [divmod_sub_coeff]
-- --     rw [smul_def, mul_comm_right, ←smul_def, add_comm,
-- --       add_sub_assoc, ←sub_mul, add_comm]

-- --     sorry

-- -- def add_mod (a b: P[X]) : (a + b).mod p = a.mod p + b.mod p := by
-- --   induction a using Poly.divmod_induction p inv with
-- --   | deg_lt a ha =>
-- --     rw [mod_of_lt _ _ ha]
-- --     induction b using Poly.divmod_induction p inv with
-- --     | deg_lt b hb =>
-- --       rw [mod_of_lt, mod_of_lt _ _ hb]
-- --       apply lt_of_le_of_lt
-- --       apply Poly.add_degree
-- --       apply max_lt_iff.mpr
-- --       apply And.intro
-- --       assumption
-- --       assumption
-- --     | le_deg b hb ih =>
-- --       rw [mod_of_le _ _ hb, ←ih]
-- --       clear ih
-- --       unfold divmod_sub_coeff
-- --       simp
-- --       rw [←add_sub_assoc, smul_def, mul_comm_right, ←smul_def]
-- --       sorry
-- --   | le_deg a ha ih =>
-- --     rw [mod_of_le _ _ ha, ←ih]
-- --     clear ih
-- --     sorry

-- def div_mul_add_mod_inj (a b c d p: P[X]) (hb: b.degree < p.degree) (hd: d.degree < p.degree) :
--   a * p + b = c * p + d -> a = c ∧ b = d := by
--   intro h

--   sorry

end Poly
