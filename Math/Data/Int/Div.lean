import Math.Data.Nat.Div
import Math.Data.Int.Basic

namespace int

section div

def ofNat_pos (a: nat) : ofNat a ≠ 0 -> 0 < a := by
  intro h
  cases a using nat.cases <;> trivial
def abs_pos (a: int) : a ≠ 0 -> 0 < ‖a‖ := by
  intro h
  cases a using rec' <;> trivial

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply ofNat_pos; invert_tactic)
macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply abs_pos; invert_tactic)

noncomputable
def div (a b: int) (h: b ≠ 0) : int := by
  cases a using rec with
  | ofNat a =>
    cases b using rec with
    | ofNat b => exact ofNat (a /? b)
    | negSucc b => exact -ofNat (a /? b.succ)
  | negSucc a =>
    cases b using rec' with
    | zero => contradiction
    | posSucc b => exact -ofNat (a.succ /? b.succ)
    | negSucc b => exact ofNat (a.succ /? b.succ)

def divFast (a b: int) (_h: b ≠ 0) : int := ofInt (a.toInt.tdiv b.toInt)

@[csimp]
def div_eq_divFast : div = divFast := by
  funext a b h
  unfold div divFast
  unfold Int.tdiv
  cases a using rec with
  | ofNat a =>
    cases b using rec with
    | ofNat b =>
      show ofNat (nat.div _ _ _) = _
      rw [nat.div_eq_fastDiv]
      rfl
    | negSucc b =>
      show neg (ofNat (nat.div _ _ _)) = ofInt (-(_ ))
      rw [nat.div_eq_fastDiv, neg_eq_negFast]
      rfl
  | negSucc a =>
    cases b using rec' with
    | zero => contradiction
    | posSucc b =>
      show neg (ofNat (nat.div _ _ _)) = _
      rw [nat.div_eq_fastDiv, neg_eq_negFast]
      rfl
    | negSucc b =>
      show (ofNat (nat.div _ _ _)) = _
      rw [nat.div_eq_fastDiv]
      rfl

instance : CheckedDiv int (fun x => x ≠ 0) where
  checked_div := div

def div_abs (a b: int) (h: b ≠ 0) : ‖a /? b‖ = ‖a‖ /? ‖b‖ := by
  cases a using rec
  · cases b using rec
    rfl
    rename_i a b
    show ‖div _ _ _‖ = _ /? b.succ
    unfold div
    simp [rec]
    rw [←neg_ofNat, abs_neg]
    rfl
  · cases b using rec'
    contradiction
    rename_i a b
    show ‖-(ofNat _)‖ = a.succ /? b.succ
    rw [abs_neg]
    rfl
    rename_i a b
    show ‖(ofNat _)‖ = a.succ /? b.succ
    rfl

def div_den_congr (a b c: int) (e: b = c) (h: b ≠ 0) (g: c ≠ 0) : a /? b = a /? c := by
  cases e
  rfl

def ofNat_div (a b: nat) (h: 0 < b) : ofNat a /? ofNat b ~(by intro h; cases h; contradiction) = ofNat (a /? b) := by
  rfl

end div

end int
