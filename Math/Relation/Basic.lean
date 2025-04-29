import Math.Relation.RelIso
import Math.Type.Notation

def Nat.strict_dvd (a b: ℕ) : Prop := Relation.strict (· ∣ ·) a b

instance : Relation.IsWellFounded Nat.strict_dvd where
  wf := by
    apply WellFounded.intro
    suffices ∀n, n ≠ 0 -> Acc Nat.strict_dvd n by
      intro n
      refine if hn:n = 0 then ?_ else ?_
      subst n
      apply Acc.intro
      intro m ⟨m_dvd_n, n_not_dvd_m⟩
      dsimp at *
      cases m
      contradiction
      apply this
      nofun
      apply this
      assumption
    intro n hn
    induction n using Nat.strongRecOn with
    | ind n ih =>
    apply Acc.intro
    intro m ⟨m_dvd_n, n_not_dvd_m⟩
    dsimp at *
    apply ih
    cases n
    contradiction
    cases m
    apply Nat.zero_lt_succ
    rename_i n m
    apply Nat.lt_of_le_of_ne
    apply Nat.le_of_dvd
    apply Nat.zero_lt_succ
    assumption
    intro h
    cases Nat.succ.inj h
    contradiction
    rintro rfl
    rw [Nat.zero_dvd] at m_dvd_n
    contradiction

instance : Relation.IsTop Nat.strict_dvd (· = ·) 0 where
  is_top _ h := ⟨Nat.dvd_zero _, fun g => h (Nat.zero_dvd.mp g)⟩

def Int.strict_dvd (a b: ℤ) : Prop := Relation.strict (· ∣ ·) a b

def Int.strict_dvd_to_nat_strict_dvd : Int.strict_dvd →r Nat.strict_dvd where
  toFun := Int.natAbs
  resp_rel {a b} h := by
    apply And.intro
    dsimp
    apply Int.natAbs_dvd_natAbs.mpr
    exact h.left
    intro g
    apply h.right
    apply Int.natAbs_dvd_natAbs.mp
    assumption

instance : Relation.IsWellFounded Int.strict_dvd :=
  Int.strict_dvd_to_nat_strict_dvd.wf

instance : Relation.IsTop Int.strict_dvd (· = ·) 0 where
  is_top _ h := ⟨Int.dvd_zero _, fun g => h (Int.zero_dvd.mp g)⟩

def Int.abs_lt (a b: ℤ) : Prop := a.natAbs < b.natAbs

def Int.abs_lt_to_nat_lt : Int.abs_lt →r (· < ·: ℕ -> ℕ -> Prop) where
  toFun := Int.natAbs
  resp_rel h := h

instance : Relation.IsWellFounded Int.abs_lt :=
  Int.abs_lt_to_nat_lt.wf
