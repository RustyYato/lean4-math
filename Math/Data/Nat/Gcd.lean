import Math.Data.Nat.Div

namespace nat

def gcd (a b: nat) :=
  if h:0 < a then
    gcd (b %? a) a
  else
    b
termination_by a
decreasing_by exact nat.mod_lt _ _ _

def gcdFast (a b: nat) := ofNat (a.toNat.gcd b.toNat)

def gcd.ind
  (motive: nat -> nat -> Prop)
  (zero: ∀a, motive 0 a)
  (pos: ∀a b, (h: 0 < a) -> motive (b %? a) a -> motive a b)
  (a b: nat): motive a b := by
  induction a, b using gcd.induct with
  | case2 a b h =>
    cases le_zero _ (le_of_not_lt h)
    apply zero
  | case1 a b h ih =>
    apply pos
    assumption

@[csimp]
def gcd_eq_gcdFast : gcd = gcdFast := by
  funext a b
  induction a, b using gcd.ind with
  | zero b =>
    unfold gcd gcdFast Nat.gcd
    rw [dif_neg, if_pos]
    rfl
    rfl
    apply lt_irrefl
  | pos a b h ih =>
    unfold gcd gcdFast Nat.gcd
    rw [if_neg, dif_pos h]
    rw [ih]
    · unfold gcdFast
      congr
      unfold CheckedMod.checked_mod instCheckedModLtOfNat_1
      dsimp
      rw [mod_eq_fastMod]
      rfl
    intro h
    cases h
    contradiction

def zero_gcd : gcd 0 a = a := by
  unfold gcd
  rw [dif_neg]
  apply lt_irrefl

def pos_gcd (a b: nat) (ha: 0 < a) : gcd a b = gcd (b %? a) a := by
  rw [gcd, dif_pos]

def dvd_gcd : ∀k, k ∣ a -> k ∣ b -> k ∣ gcd a b := by
  intro k ka kb
  induction a, b using gcd.ind with
  | zero b =>
    rw [zero_gcd]
    assumption
  | pos a b h ih =>
    rw [pos_gcd _ _ h]
    apply ih
    apply dvd_mod
    all_goals assumption

def gcd_dvd_args (a b: nat) : gcd a b ∣ a ∧ gcd a b ∣ b := by
  induction a, b using gcd.ind with
  | zero b =>
    rw [zero_gcd]
    apply And.intro
    apply dvd_zero
    rfl
  | pos a b h ih =>
    rw [pos_gcd _ _ h]
    obtain ⟨dvd_rem, dvd_a⟩ := ih
    apply And.intro
    assumption
    conv => { rhs; rw [←div_add_mod b a h] }
    apply dvd_add
    apply dvd_trans
    exact dvd_a
    apply dvd_mul_right
    assumption

@[simp]
def gcd_dvd_left (a b: nat) : gcd a b ∣ a := (gcd_dvd_args a b).left
@[simp]
def gcd_dvd_right (a b: nat) : gcd a b ∣ b := (gcd_dvd_args a b).right

def gcd_dvd : ∀k, a ∣ k ∨ b ∣ k -> gcd a b ∣ k := by
  intro k h
  cases h <;> rename_i h
  apply dvd_trans _ h
  apply gcd_dvd_left
  apply dvd_trans _ h
  apply gcd_dvd_right

def gcd_comm (a b: nat) : gcd a b = gcd b a := by
  apply dvd_antisymm
  apply dvd_gcd <;> simp
  apply dvd_gcd <;> simp

def gcd_assoc (a b c: nat) : gcd (gcd a b) c = gcd a (gcd b c) := by
  apply dvd_antisymm
  repeat any_goals apply dvd_gcd
  repeat any_goals first|apply gcd_dvd|simp
  right; rfl
  left; rfl

instance : Std.Commutative gcd := ⟨gcd_comm⟩
instance : Std.Associative gcd := ⟨gcd_assoc⟩

end nat
