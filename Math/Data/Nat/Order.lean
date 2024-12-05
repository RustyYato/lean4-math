import Math.Order.Linear
import Math.Data.Nat.Basic
import Math.Relation.RelIso

inductive nat.LT : nat -> nat -> Prop where
| zero : LT 0 (.succ x)
| succ {a b: nat} : LT a b -> LT a.succ b.succ

inductive nat.LE : nat -> nat -> Prop where
| zero : LE 0 x
| succ {a b: nat} : LE a b -> LE a.succ b.succ

instance : LT nat := ⟨nat.LT⟩
instance : LE nat := ⟨nat.LE⟩

def nat.LT_iff_toNat_lt (a b: nat) : a < b ↔ a.toNat < b.toNat := by
  apply Iff.intro
  intro h
  induction h
  rw [nat.toNat_succ]
  apply Nat.zero_lt_succ
  rw [nat.toNat_succ, nat.toNat_succ]
  apply Nat.succ_lt_succ
  assumption
  intro h
  induction b using rec generalizing a with
  | zero => contradiction
  | succ b ih =>
    cases a using cases
    apply nat.LT.zero
    apply nat.LT.succ
    apply ih
    apply Nat.lt_of_succ_lt_succ
    assumption

def nat.LE_iff_toNat_le (a b: nat) : a ≤ b ↔ a.toNat ≤ b.toNat := by
  apply Iff.intro
  intro h
  induction h
  apply Nat.zero_le
  rw [nat.toNat_succ, nat.toNat_succ]
  apply Nat.succ_le_succ
  assumption
  intro h
  induction a using rec generalizing b with
  | zero => apply nat.LE.zero
  | succ b ih =>
    cases b using cases
    contradiction
    apply nat.LE.succ
    apply ih
    apply Nat.le_of_succ_le_succ
    assumption

def nat.lt_reliso : ((·: nat) < ·) ≃r ((·: Nat) < ·) := by
  apply RelIso.mk nat.iso
  apply nat.LT_iff_toNat_lt

def nat.le_reliso : ((·: nat) ≤ ·) ≃r ((·: Nat) ≤ ·) := by
  apply RelIso.mk nat.iso
  apply nat.LE_iff_toNat_le

instance (a b: nat) : Decidable (a < b) := decidable_of_iff (a.toNat < b.toNat)
  (nat.LT_iff_toNat_lt _ _).symm
instance (a b: nat) : Decidable (a ≤ b) := decidable_of_iff (a.toNat ≤ b.toNat)
  (nat.LE_iff_toNat_le _ _).symm

instance : Min nat := minOfLe
instance : Max nat := maxOfLe

instance : IsLinearOrder nat where
  lt_iff_le_and_not_le := by
    intro a b
    apply Iff.intro
    intro h
    · induction h with
      | zero =>
        apply And.intro
        apply nat.LE.zero
        exact nofun
      | succ _ ih =>
        obtain ⟨ab, nba⟩ := ih
        apply And.intro
        apply nat.LE.succ
        assumption
        intro h
        cases h
        contradiction
    · intro ⟨h, g⟩
      induction h with
      | zero =>
        rename_i a
        cases a using nat.cases
        contradiction
        apply nat.LT.zero
      | succ _ ih =>
        apply nat.LT.succ
        apply ih
        intro h
        apply g
        apply nat.LE.succ
        assumption
  le_antisymm := by
    intro a b ab ba
    induction ab
    cases ba
    rfl
    cases ba
    rename_i ih _
    rw [ih]
    assumption
  lt_or_le := by
    intro a b
    induction a using nat.rec generalizing b with
    | zero =>
      cases b using nat.cases with
      | zero => right; apply nat.LE.zero
      | succ b => left; apply nat.LT.zero
    | succ a ih =>
      cases b using nat.cases with
      | zero => right; apply nat.LE.zero
      | succ b =>
        rcases ih b with ab | ba
        left; apply nat.LT.succ; assumption
        right; apply nat.LE.succ; assumption
  le_trans := by
    intro a b c ab bc
    induction ab generalizing c with
    | zero => apply nat.LE.zero
    | succ _ ih =>
      cases bc
      apply nat.LE.succ
      apply ih
      assumption

instance : IsDecidableLinearOrder nat where

section

variable {a b c: nat}

def nat.zero_le (a: nat) : 0 ≤ a := nat.LE.zero
def nat.zero_lt_succ (a: nat) : 0 < a.succ := nat.LT.zero
def nat.not_lt_zero (a: nat) : ¬a < 0 := nofun
def nat.le_zero (a: nat) : a ≤ 0 -> a = 0 := by
  intro h
  cases h
  rfl

macro_rules
| `(tactic|trivial) => `(tactic|apply nat.zero_le)
macro_rules
| `(tactic|trivial) => `(tactic|apply nat.zero_lt_succ)
macro_rules
| `(tactic|contradiction) => `(tactic|exfalso; apply nat.not_lt_zero; assumption)

def nat.succ_lt_succ : a < b -> a.succ < b.succ := nat.LT.succ
def nat.succ_le_succ : a ≤ b -> a.succ ≤ b.succ := nat.LE.succ
def nat.lt_of_succ_lt_succ : a.succ < b.succ -> a < b | .succ h => h
def nat.le_of_succ_le_succ : a.succ ≤ b.succ -> a ≤ b | .succ h => h
def nat.le_of_lt_succ : a < b.succ -> a ≤ b := by
  intro h
  induction a using nat.rec generalizing b with
  | zero => apply nat.zero_le
  | succ a ih =>
    cases h
    cases b using nat.cases
    contradiction
    apply nat.succ_le_succ
    apply ih
    assumption
def nat.lt_of_succ_le : a.succ ≤ b -> a < b := by
  intro h
  induction b using nat.rec generalizing a with
  | zero => contradiction
  | succ a ih =>
    cases h
    cases a using nat.cases
    apply nat.LT.zero
    apply nat.succ_lt_succ
    apply ih
    assumption
def nat.lt_succ_of_le : a ≤ b -> a < b.succ := by
  intro h
  apply nat.lt_of_succ_le
  apply nat.succ_le_succ
  assumption

def nat.succ_le_of_lt : a < b -> a.succ ≤ b := by
  intro h
  apply nat.le_of_lt_succ
  apply nat.succ_lt_succ
  assumption

def nat.lt_succ_self (a: nat) : a < a.succ := by
  induction a using rec with
  | zero => apply nat.zero_lt_succ
  | succ a ih =>
    apply nat.succ_lt_succ
    assumption

def nat.le_succ_self (a: nat) : a ≤ a.succ := by
  apply le_of_lt
  apply nat.lt_succ_self

def nat.lt_iff_succ_lt_succ : a < b ↔ a.succ < b.succ := ⟨nat.succ_lt_succ, nat.lt_of_succ_lt_succ⟩
def nat.le_iff_succ_le_succ : a ≤ b ↔ a.succ ≤ b.succ := ⟨nat.succ_le_succ, nat.le_of_succ_le_succ⟩

end

instance : WellFoundedRelation nat where
  rel a b := a < b
  wf := by
    apply WellFounded.intro
    intro a
    induction a using nat.rec with
    | zero =>
      apply Acc.intro
      intro b
      exact nofun
    | succ _ ih =>
      apply Acc.intro
      intro b h
      cases h
      apply Acc.intro
      exact nofun
      apply Acc.intro
      intro b b_lt_a
      apply Acc.inv
      apply ih
      rename_i h
      exact lt_of_le_of_lt (nat.le_of_lt_succ b_lt_a) h

section add

def nat.le_add_left (a b: nat) : a ≤ b + a := by
  induction b using rec with
  | zero => rfl
  | succ k ih =>
    apply le_trans ih
    apply le_succ_self
def nat.le_add_right (a b: nat) : a ≤ a + b := by
  rw [add_comm]
  apply le_add_left

def nat.add_pos (a b: nat) : 0 < a ∨ 0 < b -> 0 < a + b := by
  intro h
  cases a using cases
  cases b using cases
  contradiction
  rw [add_succ]
  apply zero_lt_succ
  apply zero_lt_succ

def nat.le_iff_exists_add_eq {a b: nat} : a ≤ b ↔ ∃k, a + k = b := by
  apply Iff.intro
  intro h
  induction h with
  | zero => refine ⟨_, rfl⟩
  | succ _ ih =>
    obtain ⟨k, prf⟩ := ih
    exists k
    rw [nat.succ_add, prf]
  intro ⟨k, eq⟩
  subst b
  apply nat.le_add_right

def nat.lt_iff_exists_add_eq {a b: nat} : a < b ↔ ∃k: nat, a + k.succ = b := by
  apply Iff.intro
  intro h
  induction h with
  | zero => refine ⟨_, rfl⟩
  | succ _ ih =>
    obtain ⟨k, prf⟩ := ih
    exists k
    rw [nat.succ_add, prf]
  intro ⟨k, eq⟩
  subst b
  apply lt_of_le_of_lt
  apply nat.le_add_right _ k
  rw [add_succ]
  apply nat.lt_succ_self

def nat.eq_zero_of_add_le_self {a b: nat} : a + b ≤ a -> b = 0 := by
  intro ab_le_a
  cases b using cases
  rfl
  rw [add_succ, ←succ_add] at ab_le_a
  have := le_trans (le_add_right _ _) ab_le_a
  have := not_lt_of_le this (lt_succ_self _)
  contradiction

def nat.le_add_left_of_le (a b k: nat) : a ≤ b -> k + a ≤ k + b := by
  intro h
  induction k using rec with
  | zero => assumption
  | succ k ih =>
    apply nat.succ_le_succ
    assumption

def nat.lt_add_left_of_lt (a b k: nat) : a < b -> k + a < k + b := by
  intro h
  induction k using rec with
  | zero => assumption
  | succ k ih =>
    apply nat.succ_lt_succ
    assumption

def nat.le_add_right_of_le (a b k: nat) : a ≤ b -> a + k ≤ b + k := by
  intro h
  rw [add_comm _ k, add_comm _ k]
  apply le_add_left_of_le
  assumption

def nat.lt_add_right_of_lt (a b k: nat) : a < b -> a + k < b + k := by
  intro h
  rw [add_comm _ k, add_comm _ k]
  apply lt_add_left_of_lt
  assumption

def nat.add_le_add (a b c d: nat) : a ≤ c -> b ≤ d -> a + b ≤ c + d := by
  intro ac bd
  apply le_trans
  apply le_add_left_of_le
  assumption
  apply le_add_right_of_le
  assumption

def nat.add_lt_add (a b c d: nat) : a < c -> b < d -> a + b < c + d := by
  intro ac bd
  apply lt_trans
  apply lt_add_left_of_lt
  assumption
  apply lt_add_right_of_lt
  assumption

def nat.add_lt_add_of_le_of_lt (a b c d: nat) : a ≤ c -> b < d -> a + b < c + d := by
  intro ac bd
  apply lt_of_lt_of_le
  apply lt_add_left_of_lt
  assumption
  apply le_add_right_of_le
  assumption

def nat.add_lt_add_of_lt_of_le (a b c d: nat) : a < c -> b ≤ d -> a + b < c + d := by
  intro ac bd
  apply lt_of_le_of_lt
  apply le_add_left_of_le
  assumption
  apply lt_add_right_of_lt
  assumption

def nat.le_add_left_iff_le {a b k: nat} : a ≤ b ↔ k + a ≤ k + b := by
  apply Iff.intro (nat.le_add_left_of_le _ _ _)
  intro h
  induction k using rec with
  | zero => assumption
  | succ k ih => exact ih (nat.le_of_succ_le_succ h)

def nat.lt_add_left_iff_lt {a b k: nat} : a < b ↔ k + a < k + b := by
  apply Iff.intro (nat.lt_add_left_of_lt _ _ _)
  intro h
  induction k using rec with
  | zero => assumption
  | succ k ih => exact ih (nat.lt_of_succ_lt_succ h)

def nat.le_add_right_iff_le {a b k: nat} : a ≤ b ↔ a + k ≤ b + k := by
  rw [add_comm _ k, add_comm _ k]
  apply nat.le_add_left_iff_le

def nat.lt_add_right_iff_lt {a b k: nat} : a < b ↔ a + k < b + k := by
  rw [add_comm _ k, add_comm _ k]
  apply nat.lt_add_left_iff_lt

def nat.add_left_cancel_iff {a b k: nat} : k + a = k + b ↔ a = b := by
  apply flip Iff.intro
  intro h
  subst h
  rfl
  intro h
  induction a using rec generalizing b with
  | zero =>
    rw [add_zero] at h
    cases b using cases with
    | zero => rfl
    | succ b =>
      exfalso
      have : k < k + b.succ := by
        conv => { lhs; rw [←add_zero k] }
        apply add_lt_add_of_le_of_lt
        rfl
        trivial
      rw [←h] at this
      have := lt_irrefl this
      contradiction
  | succ a ih =>
    cases b using cases with
    | zero =>
      exfalso
      have : k < k + a.succ := by
        conv => { lhs; rw [←add_zero k] }
        apply add_lt_add_of_le_of_lt
        rfl
        trivial
      rw [h, add_zero] at this
      have := lt_irrefl this
      contradiction
    | succ b =>
      congr
      apply ih
      apply succ.inj
      rw [add_succ, add_succ] at h
      assumption

def nat.add_right_cancel_iff {a b k: nat} : a + k = b + k ↔ a = b := by
  simp [add_comm _ k, add_left_cancel_iff]

end add

section mul

variable {a b c d k: nat}

def nat.le_mul_left : 0 < b -> a ≤ b * a := by
  intro h
  cases h
  rw [succ_mul]
  apply le_add_right

def nat.mul_pos : 0 < a -> 0 < b -> 0 < a * b := by
  intro h g
  cases h; cases g
  rw [succ_mul, mul_succ, succ_add]
  apply nat.zero_lt_succ

def nat.of_mul_pos : 0 < a * b -> 0 < a ∧ 0 < b := by
  intro h
  cases a using nat.cases
  rw [zero_mul] at h
  contradiction
  cases b using nat.cases
  rw [mul_zero] at h
  contradiction
  apply And.intro <;> trivial

def nat.lt_mul_left : 0 < a -> 1 < b -> a < a * b := by
  intro h g
  cases g; rename_i g
  replace g : (0: nat) < _ := g
  cases g
  rw [mul_succ]
  conv => { lhs; rw [←nat.add_zero a] }
  cases h
  apply nat.add_lt_add_of_le_of_lt
  rfl
  apply nat.mul_pos <;> apply nat.zero_lt_succ

def nat.lt_mul_right : 1 < a -> 0 < b -> b < a * b := by
  intro h g
  rw [mul_comm]
  apply nat.lt_mul_left <;> assumption

def nat.le_mul_left_of_le : a ≤ b -> k * a ≤ k * b := by
  intro h
  induction k using rec with
  | zero => rfl
  | succ k ih =>
    rw [succ_mul, succ_mul]
    apply nat.add_le_add <;> assumption

def nat.le_mul_right_of_le : a ≤ b -> a * k ≤ b * k := by
  intro h
  rw [mul_comm _ k, mul_comm _ k]
  apply le_mul_left_of_le
  assumption

def nat.mul_le_mul : a ≤ c -> b ≤ d -> a * b ≤ c * d := by
  intro ac bd
  apply le_trans
  apply nat.le_mul_left_of_le
  assumption
  apply nat.le_mul_right_of_le
  assumption

def nat.lt_mul_left_iff_lt (kpos: 0 < k) : (a < b ↔ k * a < k * b) := by
  induction a using nat.rec generalizing b k with
  | zero =>
    rw [mul_zero]
    apply Iff.intro
    intro h
    apply mul_pos <;> assumption
    intro h
    obtain ⟨_, _⟩ := of_mul_pos h
    assumption
  | succ a ih =>
    cases b using nat.cases with
    | zero =>
      rw [mul_zero]
      apply Iff.intro <;> (intro; contradiction)
    | succ b =>
      apply Iff.trans nat.lt_iff_succ_lt_succ.symm
      rw [mul_succ, mul_succ]
      apply flip Iff.trans
      apply nat.lt_add_left_iff_lt
      apply ih
      assumption

def nat.lt_mul_right_iff_lt (kpos: 0 < k) : (a < b ↔ a * k < b * k) := by
  rw [mul_comm _ k, mul_comm _ k]
  apply lt_mul_left_iff_lt
  assumption

def nat.mul_left_cancel_iff {a b k: nat} (h: 0 < k) : k * a = k * b ↔ a = b := by
  apply Iff.intro
  intro g
  induction a using nat.rec generalizing b with
  | zero =>
    rw [mul_zero] at g
    cases of_mul_eq_zero g.symm
    subst k
    contradiction
    symm; assumption
  | succ a ih =>
    cases b using cases with
    | zero =>
      rw [mul_zero] at g
      cases of_mul_eq_zero g
      subst k
      contradiction
      contradiction
    | succ b =>
      congr
      apply ih
      rw [mul_succ, mul_succ] at g
      apply add_left_cancel_iff.mp
      assumption
  intro h
  rw [h]

end mul

section sub

def nat.sub_add_cancel (a b: nat) (h: b ≤ a) : a - b + b = a := by
  induction h with
  | zero => simp
  | succ _ ih =>  simp [ih]

def nat.sub_le (a b: nat) : a - b ≤ a := by
  induction b using rec generalizing a with
  | zero => rfl
  | succ b ih =>
    cases a using cases
    rw [zero_sub]
    rw [succ_sub_succ]
    apply le_trans
    apply ih
    apply le_succ_self

end sub
