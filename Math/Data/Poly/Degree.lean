import Math.Data.Poly.Defs

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

def degree_lt (p: P[X]) : ∀x: ℕ, p.degree < x -> p.toFinsupp x = 0 := by
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
  rw [degree_lt]; rfl
  rw [h]
  apply lt_of_le_of_ne
  apply bot_le
  apply Option.noConfusion

end

end Poly
