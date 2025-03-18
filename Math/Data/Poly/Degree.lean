import Math.Data.Poly.Defs
import Math.Data.Nat.Basic
import Math.Order.TopBot.Linear
import Math.Data.FinSupp.Fintype

namespace Poly

section

variable [Zero P] [∀x: P, Decidable (x = 0)]

private def findDegree (p: Nat -> P) : Nat -> WithBot Nat
| 0 => ⊥
| x + 1 =>
    if p x = 0 then
      findDegree p x
    else
      WithBot.of x

def degree (p: P[X]) : WithBot Nat :=
  p.toFinsupp.spec.lift (fun x => findDegree p.toFinsupp x.val) <| by
    suffices ∀adeg bdeg: Nat,
      adeg ≤ bdeg ->
      (∀ (x : ℕ), p.toFinsupp x ≠ 0 → x ∈ adeg) ->
      (∀ (x : ℕ), p.toFinsupp x ≠ 0 → x ∈ bdeg) ->
      Poly.findDegree p.toFinsupp adeg = Poly.findDegree p.toFinsupp bdeg by
      intro ⟨adeg, ha⟩ ⟨bdeg, hb⟩
      rcases Nat.le_total adeg bdeg with h | h
      apply this <;> assumption
      symm; apply this <;> assumption
    intro adeg bdeg aleb ha hb
    induction bdeg generalizing adeg with
    | zero =>
      cases Nat.le_zero.mp aleb
      rfl
    | succ bdeg ih =>
      cases adeg with
      | zero =>
        conv => { rhs; unfold Poly.findDegree }
        split
        apply ih
        apply Nat.zero_le
        intro x hx
        have := ha x hx
        contradiction
        intro x hx
        have := ha x hx
        contradiction
        rename_i h
        have := ha _ h
        contradiction
      | succ adeg =>
        replace aleb := Nat.le_of_succ_le_succ aleb
        unfold Poly.findDegree
        split <;> split
        · apply ih
          assumption
          intro x hx
          have := ha _ hx; rw [Nat.mem_iff_lt, Nat.lt_succ,
            Nat.le_iff_lt_or_eq] at this
          cases this
          rw [Nat.mem_iff_lt]; assumption
          subst x; contradiction
          intro x hx
          have := hb _ hx; rw [Nat.mem_iff_lt, Nat.lt_succ,
            Nat.le_iff_lt_or_eq] at this
          cases this
          rw [Nat.mem_iff_lt]; assumption
          subst x; contradiction
        · rename_i h
          have := ha _ h; rw [Nat.mem_iff_lt, Nat.lt_succ] at this
          cases Nat.le_antisymm aleb this
          contradiction
        · rename_i g h
          rw [Nat.le_iff_lt_or_eq] at aleb
          rcases aleb with altb | rfl
          have aleb := Nat.succ_le_of_lt altb
          rw [←ih _ aleb ha ?_]
          unfold Poly.findDegree
          rw [if_neg]
          assumption
          intro x hx
          have := ha x hx; rw [Nat.mem_iff_lt, Nat.lt_succ] at this
          rw [Nat.mem_iff_lt]; apply Nat.lt_of_le_of_lt
          assumption
          assumption
          contradiction
        · rename_i h
          have := ha _ h; rw [Nat.mem_iff_lt, Nat.lt_succ] at this
          cases Nat.le_antisymm aleb this
          rfl

def degreeNat (p: P[X]) : Nat :=
  match p.degree with
  | .of x => x
  | .none => 0

def of_degree_lt (p: P[X]) : ∀x: ℕ, p.degree < x -> p.toFinsupp x = 0 := by
  intro x hx
  cases p with | ofFinsupp p =>
  cases p with | mk p spec =>
  induction spec with | mk spec =>
  obtain ⟨deg, spec⟩ := spec
  show p x = 0
  replace hx: findDegree p deg < _ := hx
  replace spec := fun x => Classical.contrapositive.mpr (spec x)
  conv at spec => { intro x; rw [Nat.mem_iff_lt, Nat.not_lt, Classical.not_not] }
  replace spec := spec x
  induction deg with
  | zero =>
    apply spec
    apply Nat.zero_le
  | succ deg ih =>
    unfold Poly.findDegree at hx
    split at hx
    by_cases hx':x = deg
    subst x
    assumption
    apply ih hx
    intro h
    apply spec
    apply Nat.succ_le.mpr
    cases Nat.lt_or_eq_of_le h
    assumption
    subst x
    contradiction
    rename_i h
    apply spec
    cases hx with | of hx =>
    apply Nat.succ_le_of_lt
    assumption

def degree_is_minimal (p: P[X]) (deg: WithBot Nat) : (∀x: ℕ, deg < x -> p.toFinsupp x = 0) -> p.degree ≤ deg := by
  intro h
  cases deg with
  | bot =>
    suffices p = 0 by rw [this]; rfl
    apply AddMonoidAlgebra.toFinsupp_inj
    ext i
    rw [h]; rfl
    apply WithBot.LT.bot
  | of deg =>
  cases p with | ofFinsupp p =>
  cases p with | mk p spec =>
  induction spec with | mk spec =>
  obtain ⟨pdeg, spec⟩ := spec
  show findDegree p pdeg ≤ _
  replace h : ∀x, deg < x -> p x = 0 := by
    intro x g
    apply h
    apply WithBot.LT.of
    assumption
  conv at spec => { intro ; rw [Nat.mem_iff_lt] }
  induction pdeg with
  | zero => apply bot_le
  | succ pdeg ih =>
    unfold Poly.findDegree
    split
    apply ih
    intro x h
    cases Nat.lt_or_eq_of_le (Nat.lt_succ.mp (spec x h))
    assumption
    subst x
    contradiction
    rename_i g
    have := Classical.contrapositive.mpr (h pdeg) g
    rw [Nat.not_lt] at this
    apply WithBot.LE.of
    assumption

def degree_eq_bot_iff_eq_zero {p: P[X]} : p.degree = ⊥ ↔ p = 0 := by
  apply flip Iff.intro
  rintro rfl; rfl
  intro h
  apply AddMonoidAlgebra.toFinsupp_inj
  ext x
  rw [of_degree_lt]; rfl
  rw [h]
  apply lt_of_le_of_ne
  apply bot_le
  apply Option.noConfusion

def degree_eq_degreeNat (p: P[X]) (h: ⊥ < p.degree) : p.degree = p.degreeNat := by
  unfold degreeNat
  split
  assumption
  rename_i g; rw [g] at h
  contradiction

def coeff_degreeNat_ne_zero (p: P[X]) (h: ⊥ < p.degree) : p.toFinsupp p.degreeNat ≠ 0 := by
  intro g
  cases hd:p.degree with
  | bot => rw [hd] at  h; contradiction
  | of d =>
    have hd' := hd
    rw [degree_eq_degreeNat _ h] at hd'
    replace hd' := Option.some.inj hd'
    rw [hd'] at g
    clear hd'
    clear h
    cases d
    · suffices p = 0 by
        subst p
        contradiction
      apply AddMonoidAlgebra.ext
      intro i
      cases i
      assumption
      show p.toFinsupp _ = _
      rw [p.of_degree_lt]; rfl
      rw [hd]; apply WithBot.LT.of
      apply Nat.zero_lt_succ
    · rename_i d
      suffices p.degree = d by
        rw [this] at hd
        nomatch hd
      apply flip le_antisymm
      rw [hd]; apply WithBot.LE.of
      apply Nat.le_succ
      apply degree_is_minimal
      intro x h
      cases h; rename_i h
      cases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt h) <;> rename_i h
      · rw [of_degree_lt]
        rw [hd]
        apply WithBot.LT.of
        assumption
      · subst x
        assumption

def degree_lt (p: P[X]) (deg: Nat) : (∀x: ℕ, deg ≤ x -> p.toFinsupp x = 0) -> p.degree < deg := by
  intro h
  apply lt_of_le_of_ne
  apply degree_is_minimal
  intro x g
  apply h
  cases g; apply le_of_lt; assumption
  intro g
  have degnat : p.degreeNat = deg := by
    unfold degreeNat
    split
    rw [g] at *
    rename_i h; cases h; rfl
    rw [g] at *; contradiction
  have := p.coeff_degreeNat_ne_zero ?_
  rw [degnat]  at this
  exact this (h deg (Nat.le_refl _))
  rw [g]
  apply WithBot.LT.bot

def le_degree (p: P[X]) (i: Nat) : p.toFinsupp i ≠ 0 -> i ≤ p.degree := by
  intro h
  apply le_of_not_lt
  intro g
  have := of_degree_lt _ _ g
  contradiction

def of_mem_support (p: P[X]) : ∀x, x ∈ p.toFinsupp.support -> x ≤ p.degree := by
  intro i
  rw [Finsupp.mem_support]
  intro h
  apply le_degree
  assumption

instance [Repr P] : Repr P[X] where
  reprPrec p _ :=
    Nat.fold (p.degreeNat + 1) (fun i _ ih =>
      if p.toFinsupp i = 0 then
        ih
      else if i = 0 then
        reprStr (p.toFinsupp i)
      else
        ih ++ (if ih.isEmpty  then "" else " + ") ++ reprStr (p.toFinsupp i) ++ " X^" ++ reprStr i) ""

end

def degree_add : WithBot Nat -> WithBot Nat -> WithBot Nat
| .of a, .of b => .of (a + b)
| _, _ => ⊥

def mul_degree [SemiringOps P] [IsSemiring P] [NoZeroDivisors P] [∀x: P, Decidable (x = 0)] (a b: P[X]) : (a * b).degree = degree_add a.degree b.degree := by
  apply le_antisymm
  · apply degree_is_minimal
    intro i h
    rw [AddMonoidAlgebra.mul_def, AddMonoidAlgebra.mul']
    rw [AddMonoidAlgebra.sum_toFinsupp', Finsupp.sum_eq_zero]
    intro j
    rw [AddMonoidAlgebra.sum_toFinsupp', Finsupp.sum_eq_zero]
    intro k
    simp [Finsupp.apply_single]
    rintro rfl
    cases ha:a.degree  with
    | bot =>
      rw [a.of_degree_lt, zero_mul]
      rw [ha]
      apply WithBot.LT.bot
    | of adeg =>
    cases hb:b.degree  with
    | bot =>
      rw [b.of_degree_lt, mul_zero]
      rw [hb]
      apply WithBot.LT.bot
    | of bdeg =>
      rw [ha, hb] at h
      rcases Nat.lt_or_ge adeg j with g | g
      rw [a.of_degree_lt, zero_mul]; rw [ha]
      apply WithBot.LT.of; assumption
      rw [b.of_degree_lt, mul_zero]
      cases h; rename_i h
      rw [hb]
      apply WithBot.LT.of
      omega
  · cases h:degree_add a.degree b.degree
    apply bot_le
    apply le_degree
    cases ha:a.degree  with
    | bot => rw [ha] at h; contradiction
    | of adeg =>
    cases hb:b.degree  with
    | bot => rw [ha, hb] at h; contradiction
    | of bdeg =>
      rw [ha, hb] at h
      cases h
      rw [AddMonoidAlgebra.mul_def, AddMonoidAlgebra.mul']
      rw [
        AddMonoidAlgebra.sum_toFinsupp',
        Finsupp.sum_eq_fintypesum]
      conv => {
        lhs; arg 1; intro i
        rw [AddMonoidAlgebra.sum_toFinsupp', Finsupp.sum_eq_fintypesum]
        arg 1; intro j
        erw [AddMonoidAlgebra.apply_single]
      }
      have adegnat : a.degreeNat = adeg := by
          have h := ha
          rw [a.degree_eq_degreeNat] at h
          rw [←Option.some.inj h]
          rw [ha]
          apply WithBot.LT.bot
      have bdegnat : b.degreeNat = bdeg := by
          have h := hb
          rw [b.degree_eq_degreeNat] at h
          rw [←Option.some.inj h]
          rw [hb]
          apply WithBot.LT.bot
      classical
      rw [sum_sum, sum_select_unique (fi := fun i: a.toFinsupp.support × b.toFinsupp.support => adeg + bdeg = i.fst.val + i.snd.val)
        (i₀ := (⟨a.degreeNat, (by
          rw [Finsupp.mem_support]
          apply a.coeff_degreeNat_ne_zero
          rw [ha]; apply WithBot.LT.bot)⟩ , ⟨b.degreeNat, (by
          rw [Finsupp.mem_support]
          apply b.coeff_degreeNat_ne_zero
          rw [hb]; apply WithBot.LT.bot)⟩))]
      simp
      intro h
      rcases of_mul_eq_zero h with h | h
      refine a.coeff_degreeNat_ne_zero ?_ h
      rw [ha]; apply WithBot.LT.bot
      refine b.coeff_degreeNat_ne_zero ?_ h
      rw [hb]; apply WithBot.LT.bot
      intro ⟨⟨adeg', adeg'spec⟩, ⟨bdeg', bdeg'spec⟩⟩
      simp
      replace adeg'spec := of_mem_support _ _ adeg'spec
      replace bdeg'spec := of_mem_support _ _ bdeg'spec
      subst adeg bdeg
      rw [ha] at adeg'spec
      rw [hb] at bdeg'spec
      cases adeg'spec
      cases bdeg'spec
      rename_i adeg'spec bdeg'spec
      apply Iff.intro
      intro h
      apply And.intro
      congr
      omega
      congr
      omega
      intro ⟨h₀, h₁⟩
      cases h₀; cases h₁
      rfl

def add_degree [SemiringOps P] [IsSemiring P] [∀x: P, Decidable (x = 0)] (a b: P[X]) : (a + b).degree ≤ max a.degree b.degree := by
  apply degree_is_minimal
  intro i hi
  show a.toFinsupp i + b.toFinsupp i = 0
  rw [a.of_degree_lt, b.of_degree_lt, add_zero]
  apply lt_of_le_of_lt _ hi
  apply le_max_right
  apply lt_of_le_of_lt _ hi
  apply le_max_left

def add_degree_of_ne_degree [SemiringOps P] [IsSemiring P] [∀x: P, Decidable (x = 0)] (a b: P[X]) (h: a.degree ≠ b.degree) : (a + b).degree = max a.degree b.degree := by
  revert a b
  suffices ∀a b: P[X], a.degree < b.degree -> (a + b).degree = max a.degree b.degree by
    intro a b h
    rcases lt_trichotomy a.degree b.degree with g | g | g
    apply this
    assumption
    contradiction
    rw [add_comm, max_comm]
    apply this
    assumption
  intro a b h
  apply le_antisymm
  apply add_degree
  rw [max_iff_le_left.mp (le_of_lt h)]
  cases hb:b.degree
  apply bot_le
  apply le_degree
  have := hb
  rw [degree_eq_degreeNat] at this
  cases this
  show a.toFinsupp b.degreeNat + b.toFinsupp b.degreeNat ≠ 0
  rw [of_degree_lt, zero_add]
  refine coeff_degreeNat_ne_zero b ?_
  rw [hb]; apply WithBot.LT.bot
  rw [←hb]; assumption
  rw [hb]; apply WithBot.LT.bot

def neg_degree [RingOps P] [IsRing P] [∀x: P, Decidable (x = 0)] (a: P[X]) : (-a).degree = a.degree := by
  apply le_antisymm
  apply degree_is_minimal
  intro i h
  show -a.toFinsupp i = 0
  rw [a.of_degree_lt, neg_zero]
  assumption
  apply degree_is_minimal
  intro i h
  rw [←neg_neg (a.toFinsupp i)]
  show - (-a).toFinsupp i = 0
  rw [(-a).of_degree_lt _ h, neg_zero]

def sub_degree [RingOps P] [IsRing P] [∀x: P, Decidable (x = 0)] (a b: P[X]) : (a - b).degree ≤ max a.degree b.degree := by
  rw [sub_eq_add_neg]
  apply le_trans
  apply add_degree
  rw [neg_degree]

def Xpow_degree [SemiringOps P] [IsSemiring P] [IsNontrivial P] [∀x: P, Decidable (x = 0)] (n: Nat) : (X ^ n: P[X]).degree = n := by
  apply le_antisymm
  apply degree_is_minimal
  intro i hi
  cases hi; rename_i hi
  obtain ⟨k, rfl⟩  := (Nat.le_iff_exists_sum _ _).mp (Nat.succ_le_of_lt hi)
  rw [←one_mul (X ^ n), coeff_mul_Xpow, Nat.succ_add, Nat.succ_sub]
  rfl
  apply Nat.le_add_right
  apply le_of_lt; assumption
  apply le_degree
  intro h
  rw [←one_mul (X^n), coeff_mul_Xpow, Nat.sub_self] at h
  exact zero_ne_one P h.symm
  rfl

def const_degree_ne_zero [SemiringOps P] [IsSemiring P] [∀x: P, Decidable (x = 0)] (x: P) (h: x ≠ 0) : (C x).degree = .of 0 := by
  apply le_antisymm
  · apply degree_is_minimal
    intro i h
    match i with
    | i + 1 =>
    rfl
  · apply le_degree
    assumption

def const_degree_eq [SemiringOps P] [IsSemiring P] [∀x: P, Decidable (x = 0)] (x: P) : (C x).degree = if x = 0 then ⊥ else .of 0 := by
  split
  subst x
  rw [resp_zero]; rfl
  rw [const_degree_ne_zero]
  assumption

instance [RingOps P] [IsRing P] [NoZeroDivisors P] : NoZeroDivisors P[X] where
  of_mul_eq_zero := by
    classical
    intro a b eq
    cases ha:a.degree
    left; rw [degree_eq_bot_iff_eq_zero.mp ha]
    cases hb:b.degree
    right; rw [degree_eq_bot_iff_eq_zero.mp hb]
    have := (a * b).coeff_degreeNat_ne_zero ?_
    rw [eq] at this
    contradiction
    rw [mul_degree, ha, hb]
    apply WithBot.LT.bot

def lead [Zero P] [∀x: P, Decidable (x = 0)] (p: P[X]) : P := p.toFinsupp p.degreeNat

def lead_eq_zero [Zero P] [∀x: P, Decidable (x = 0)] (p: P[X]) (h: p.degree = ⊥) : p.lead = 0 := by
  rw [degree_eq_bot_iff_eq_zero.mp h]
  rfl
def lead_nonzero [Zero P] [∀x: P, Decidable (x = 0)] (p: P[X]) (h: ⊥ < p.degree) : p.lead ≠ 0 := by
  apply coeff_degreeNat_ne_zero
  assumption
def lead_zero [Zero P] [∀x: P, Decidable (x = 0)] : lead (0: P[X]) = 0 := rfl

end Poly
