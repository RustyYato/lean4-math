import Math.Data.Int.Basic
import Math.Data.Nat.Order

namespace int

inductive NonNeg : int -> Prop where
| intro (a: nat) : NonNeg (.ofNat a)

attribute [simp] NonNeg.intro

@[simp]
instance : LE int where
  le a b := (b - a).NonNeg
@[simp]
instance : LT int where
  lt a b := a.succ ≤ b

def NonNeg_iff_toInt_Noneg (a: int) : a.NonNeg ↔ a.toInt.NonNeg := by
  apply Iff.intro
  intro ⟨h⟩
  rw [toInt_ofNat]
  apply Int.NonNeg.mk
  intro h
  cases a using rec
  apply NonNeg.intro
  contradiction

def NonNeg.iff {a: int} : a.NonNeg ↔ ∃a', a = ofNat a' := by
  apply Iff.intro
  intro ⟨a⟩
  exists a
  intro ⟨a, h⟩
  subst h
  apply NonNeg.intro

def NonNeg_iff_ofInt_Noneg (a: Int) : (ofInt a).NonNeg ↔ a.NonNeg := by
  conv => { rhs; rw [←toInt.LeftInverse a] }
  apply flip Iff.trans
  apply NonNeg_iff_toInt_Noneg
  rfl

def LE_iff_toInt_LE (a b: int) : a ≤ b ↔ a.toInt ≤ b.toInt := by
  apply Iff.trans _ (NonNeg_iff_ofInt_Noneg _)
  show _ ↔ (b.subFast a).NonNeg
  rw [←sub_eq_subFast]
  apply Iff.refl
def LT_iff_toInt_LT (a b: int) : a < b ↔ a.toInt < b.toInt := by
  show a.succ ≤ b ↔ a.toInt + 1 ≤ b.toInt
  apply Iff.trans (LE_iff_toInt_LE _ _)
  rw [toInt_succ]

def NonNeg.succ : NonNeg a -> NonNeg a.succ := by
  intro ⟨a⟩
  apply NonNeg.intro

instance decLT (a b: int) : Decidable (a < b) := decidable_of_iff _ (LT_iff_toInt_LT a b).symm
instance decLE (a b: int) : Decidable (a ≤ b) := decidable_of_iff _ (LE_iff_toInt_LE a b).symm

instance : Min int := minOfLe
instance : Max int := maxOfLe

def le_antisymm' {a b: int} : a ≤ b -> b ≤ a -> a = b := by
  intro ab ba
  replace ⟨k₀, ab⟩  := NonNeg.iff.mp ab
  replace ⟨k₁, ba⟩ := NonNeg.iff.mp ba
  have : (b - a) + (a - b) = 0 := by
    simp [sub_eq_add_neg]
    rw [add_comm_left, add_right_comm b]
    simp
  rw [ab, ba] at this
  simp at this
  have : k₀ + k₁ = 0 := by
    apply ofNat.inj
    rw [this]
    rfl
  have ⟨_, _⟩  := nat.add_eq_zero this
  subst k₀; subst k₁
  clear this; clear this
  exact sub_eq_zero_iff.mp ba

instance : IsLinearOrder int where
  lt_iff_le_and_not_le := by
    intro a b
    apply Iff.intro
    intro h
    obtain h : (b - a.succ).NonNeg := h
    have h' := h.succ
    simp at h'
    apply And.intro
    assumption
    intro g
    obtain g : (a - b).NonNeg := g
    cases le_antisymm' h' g
    simp at h
    contradiction
    intro ⟨ab, ba⟩
    have ⟨k₀, ab⟩ := NonNeg.iff.mp ab
    apply NonNeg.iff.mpr
    exists k₀.pred
    rw [sub_succ, ab]
    cases k₀ using nat.cases
    cases sub_eq_zero_iff.mp ab
    contradiction
    rfl
  le_antisymm := le_antisymm'
  le_trans := by
    intro a b c ab bc
    replace ⟨k₀, ab⟩ := NonNeg.iff.mp ab
    replace ⟨k₁, bc⟩ := NonNeg.iff.mp bc
    apply NonNeg.iff.mpr
    exists k₀ + k₁
    rw [←add_zero (c - a), ←sub_self b, sub_eq_add_neg b, ←add_assoc,
      sub_add_assoc c, sub_eq_add_neg, add_assoc, add_comm _ (-b), ←add_assoc,
      ←sub_eq_add_neg c, bc, neg_sub, ab]
    simp [nat.add_comm]
  lt_or_le := by
    intro a b
    induction b using ind generalizing a with
    | zero =>
      cases a using rec
      right; show NonNeg _; simp
      left; show NonNeg _; simp
    | succ b ih =>
      rcases ih a.pred with ab | ba
      left; simp at ab; simp [ab]
      right; simp at ba; simp [ba]
    | pred b ih =>
      rcases ih a.succ with ab | ba
      left; simp at ab; simp [ab]
      right; simp at ba; simp [ba]
instance : IsDecidableLinearOrder int where

variable {a b c d k: int}
variable {a₀ b₀ c₀ d₀: int}

def negSucc_lt_zero (x: nat) : negSucc x < 0 := by simp
def zero_lt_posSucc (x: nat) : 0 < posSucc x := by simp
def zero_le_ofNat (x: nat) : 0 ≤ ofNat x := by simp
def negSucc_lt_ofNat (x y: nat) : negSucc x < ofNat y := lt_of_lt_of_le (negSucc_lt_zero _) (zero_le_ofNat _)
def negSucc_lt_posSucc (x y: nat) : negSucc x < posSucc y := lt_trans (negSucc_lt_zero _) (zero_lt_posSucc _)

section succ_pred

def succ_lt_succ_iff_lt : a.succ < b.succ ↔ a < b := by simp
def succ_le_succ_iff_le : a.succ ≤ b.succ ↔ a ≤ b := by simp
def pred_lt_pred_iff_lt : a.pred < b.pred ↔ a < b := by simp
def pred_le_pred_iff_le : a.pred ≤ b.pred ↔ a ≤ b := by simp

def lt_succ_self (a: int) : a < a.succ := by
  simp
  show NonNeg (ofNat 0)
  apply NonNeg.intro

def pred_self_lt (a: int) : a.pred < a := by
  simp
  show NonNeg (ofNat 0)
  apply NonNeg.intro

end succ_pred

def ofNat_le_iff {a b: nat} : ofNat a ≤ ofNat b ↔ a ≤ b := by
  apply Iff.intro
  · intro h
    have ⟨k, prf⟩ := NonNeg.iff.mp h
    clear h
    induction k using nat.rec generalizing b with
    | zero =>
      cases sub_eq_zero_iff.mp prf
      rfl
    | succ k ih =>

      cases b using nat.cases
      erw [zero_sub, neg_ofNat] at prf
      cases a using nat.cases
      replace prf : ofNat 0 = ofNat _ := prf
      have := ofNat.inj prf
      contradiction
      rw [succ_negSucc_succ] at prf
      nomatch prf
      rename_i b

      have : ofNat b - ofNat a = ofNat k := by
        have : ofNat b.succ - ofNat a + -ofNat b.succ = ofNat k.succ + -ofNat b.succ := add_right_iff.mpr prf
        rw [sub_eq_add_neg, add_right_comm, add_neg_self, zero_add] at this
        rw [sub_eq_add_neg, this, ←ofNat_succ, add_comm _ (-_), ←add_assoc, add_succ, ←succ_add, ←succ_add]
        conv => { rhs; rw [←zero_add (ofNat k)] }
        congr
        rw [ofNat_succ, add_neg_self]
      apply le_trans
      show a ≤ b
      apply ih
      assumption
      apply le_of_lt
      apply nat.lt_succ_self
  · intro h
    induction h with
    | zero => apply zero_le_ofNat
    | succ h ih =>
      simp
      rw [←ofNat_succ, ←ofNat_succ, sub_succ, succ_sub, succ_pred]
      assumption

section neg

def neg_lt_neg_iff_lt : -a < -b ↔ b < a := by simp [add_comm, sub_eq_add_neg]
def neg_le_neg_iff_le : -a ≤ -b ↔ b ≤ a := by simp [add_comm, sub_eq_add_neg]
def neg_lt_symm : -a < b ↔ -b < a := by simp [add_comm, sub_eq_add_neg]
def neg_le_symm : -a ≤ b ↔ -b ≤ a := by simp [add_comm, sub_eq_add_neg]

end neg

section add

@[simp]
def lt_add_right_iff_lt : a + k < b + k ↔ a < b := by
  simp [sub_eq_add_neg _ _, neg_add, add_assoc _ k, add_comm_left k]
@[simp]
def le_add_right_iff_le : a + k ≤ b + k ↔ a ≤ b := by
  simp [sub_eq_add_neg _ _, neg_add, add_assoc _ k, add_comm_left k]

@[simp]
def lt_add_left_iff_lt : k + a < k + b ↔ a < b := by
  simp only [add_comm k, lt_add_right_iff_lt]
@[simp]
def le_add_left_iff_le : k + a ≤ k + b ↔ a ≤ b := by
  simp only [add_comm k, le_add_right_iff_le]

def add_le_add : a ≤ c -> b ≤ d -> a + b ≤ c + d := by
  intro ac bd
  apply le_trans
  apply le_add_right_iff_le.mpr
  assumption
  apply le_add_left_iff_le.mpr
  assumption

def add_lt_add : a < c -> b < d -> a + b < c + d := by
  intro ac bd
  apply lt_trans
  apply lt_add_right_iff_lt.mpr
  assumption
  apply lt_add_left_iff_lt.mpr
  assumption

def add_lt_add_of_lt_of_le : a < c -> b ≤ d -> a + b < c + d := by
  intro ac bd
  apply lt_of_lt_of_le
  apply lt_add_right_iff_lt.mpr
  assumption
  apply le_add_left_iff_le.mpr
  assumption

def add_lt_add_of_le_of_lt : a ≤ c -> b < d -> a + b < c + d := by
  intro ac bd
  apply lt_of_le_of_lt
  apply le_add_right_iff_le.mpr
  assumption
  apply lt_add_left_iff_lt.mpr
  assumption

def add_pos : 0 < a -> 0 < b -> 0 < a + b := by
  intro ha hb
  rw [←add_zero 0]
  apply add_lt_add <;> assumption

def add_le_add_iff : (a ≤ b ↔ c ≤ d) -> (a₀ ≤ b₀ ↔ c ≤ d) ->
  (a₀ + a ≤ b₀ + b ↔ c ≤ d) := by
  intro h g
  apply flip Iff.intro
  intro cd
  apply add_le_add
  exact g.mpr cd
  exact h.mpr cd
  intro hadd
  simp [sub_eq_add_neg, neg_add] at hadd
  rw [add_assoc, add_comm_left b, ←add_assoc] at hadd
  by_cases ab:a ≤ b
  apply h.mp ab
  have a₀b₀ := (Iff.not_iff_not (h.trans g.symm)).mp ab
  replace ab := lt_of_not_le ab
  replace a₀b₀ := lt_of_not_le a₀b₀
  simp at ab a₀b₀
  rw [←succ_pred (_ + _), ←succ_pred (succ _), ←succ_add, ←add_succ] at hadd
  have ⟨k₀, k₀eq⟩  := NonNeg.iff.mp ab
  have ⟨k₁, k₁eq⟩  := NonNeg.iff.mp a₀b₀
  replace k₀eq : -(a - b).pred = -ofNat k₀ := by rw [k₀eq]
  replace k₁eq: -(a₀ - b₀).pred = -ofNat k₁ := by rw [k₁eq]
  simp at k₀eq k₁eq
  simp [←sub_eq_add_neg, k₀eq, k₁eq, ←pred_add, ←add_pred] at hadd
  contradiction

end add

section mul

def le_mul_right_iff_le (hk: 0 < k) : a * k ≤ b * k ↔ a ≤ b := by
  have ⟨k₀, prf⟩  := NonNeg.iff.mp hk
  replace prf : k - 1 = ofNat k₀ := prf
  clear hk
  induction k₀ using nat.rec generalizing k with
  | zero =>
    cases sub_eq_zero_iff.mp prf
    simp
  | succ k₀ ih =>
    rw [←pred_succ k, mul_succ, mul_succ]
    apply add_le_add_iff
    rfl
    apply ih
    rw [pred_sub, prf]
    rfl

def lt_mul_right_iff_lt (h: 0 < k) : a * k < b * k ↔ a < b := by
  apply Decidable.not_iff_not.mp
  apply Iff.trans le_iff_not_lt.symm
  apply Iff.trans _ le_iff_not_lt
  apply le_mul_right_iff_le
  assumption

def le_mul_left_iff_le (hk: 0 < k) : k * a ≤ k * b ↔ a ≤ b := by
  simp only [mul_comm k, le_mul_right_iff_le hk]
def lt_mul_left_iff_lt (hk: 0 < k) : k * a < k * b ↔ a < b := by
  simp only [mul_comm k, lt_mul_right_iff_lt hk]

def mul_le_mul_of_nonneg (ha: 0 ≤ a) (hb: 0 ≤ b) : a ≤ c -> b ≤ d -> a * b ≤ c * d := by
  intro ac bd
  have ⟨a', prfa⟩  := NonNeg.iff.mp ha
  rw [sub_zero] at prfa
  subst a
  have ⟨c', prfc⟩  := NonNeg.iff.mp (le_trans ha ac)
  rw [sub_zero] at prfc
  subst c
  have ⟨b', prfc⟩  := NonNeg.iff.mp hb
  rw [sub_zero] at prfc
  subst b
  have ⟨d', prfc⟩  := NonNeg.iff.mp (le_trans hb bd)
  rw [sub_zero] at prfc
  subst d
  replace ac := ofNat_le_iff.mp ac
  replace bd := ofNat_le_iff.mp bd
  erw [ofNat_mul, ofNat_mul]
  apply ofNat_le_iff.mpr
  apply nat.mul_le_mul
  assumption
  assumption

def mul_pos : 0 < a -> 0 < b -> 0 < a * b := by
  intro ha hb
  apply lt_of_le_of_ne
  rw [←mul_zero 0]
  apply mul_le_mul_of_nonneg
  trivial
  trivial
  apply le_of_lt; assumption
  apply le_of_lt; assumption
  intro h
  cases mul_eq_zero.mp h.symm
  subst a; contradiction
  subst b; contradiction

end mul

end int
