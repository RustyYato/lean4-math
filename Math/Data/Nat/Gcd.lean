import Math.Data.Nat.Div

namespace nat

def gcd (a b: nat) :=
  if h:0 < a then
    gcd (b %? a) a
  else
    b
termination_by a
decreasing_by exact nat.mod_lt _ _ _

def Coprime (a b: nat) := gcd a b = 1

instance : Decidable (Coprime a b) := inferInstanceAs (Decidable (_ = _))

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

def gcd_dvd' : ∀k, (∀x, x ∣ a -> x ∣ b -> x ∣ k) -> gcd a b ∣ k := by
  intro k h
  induction a, b using gcd.ind generalizing k with
  | zero b =>
    rw [zero_gcd]
    apply h
    apply dvd_zero
    rfl
  | pos a b apos ih =>
    rw [pos_gcd _ _ apos]
    apply h
    apply gcd_dvd
    right; rfl
    apply ih
    intro x x_dvd_mod x_dvd_a
    apply of_dvd_mod
    assumption
    assumption

def of_gcd_dvd : ∀x, gcd a b ∣ x -> ∀k, k ∣ a -> k ∣ b -> k ∣ x := by
  intro k h k' k'a k'b
  apply dvd_trans
  show k' ∣ gcd a b
  apply dvd_gcd <;> assumption
  assumption

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

def zero_gcd_zero : gcd 0 0 = 0 := by
  unfold gcd
  rfl
def one_gcd : gcd 1 a = 1 := by
  apply dvd_one.mp
  apply gcd_dvd
  left; rfl
def gcd_one : gcd a 1 = 1 := by
  apply dvd_one.mp
  apply gcd_dvd
  right; rfl

@[symm]
def Coprime.symm : Coprime a b -> Coprime b a := by
  intro ab
  unfold Coprime
  rw [gcd_comm]
  assumption

def coprime_of_mul_right :
  Coprime (a * c) b ->
  Coprime a b := by
  unfold Coprime
  intro acb
  apply dvd_one.mp
  apply of_gcd_dvd _ (dvd_one.mpr acb)
  apply gcd_dvd
  left
  apply dvd_mul_right
  apply gcd_dvd_right

def coprime_of_mul_left :
  Coprime (a * c) b ->
  Coprime c b := by
  rw [mul_comm]
  apply coprime_of_mul_right

def coprime_of_npow_succ :
  Coprime (a^(n+1)) b ->
  Coprime a b := by
  rw [npow_succ]
  apply coprime_of_mul_right

def coprime_mul :
  Coprime a k ->
  Coprime b k ->
  Coprime (a * b) k := by
  intro ak bk
  apply dvd_one.mp
  apply gcd_dvd'
  intro x x_dvd_amul x_dvd_k
  have := (fun h => of_gcd_dvd _ (dvd_one.mpr ak) x h x_dvd_k)
  have := (fun h => of_gcd_dvd _ (dvd_one.mpr bk) x h x_dvd_k)
  sorry

def pow_coprime_iff_ne {a b: nat} {n m: Nat} :
  (a ^ n).Coprime (b ^ m) ↔ Coprime a b ∨ n = 0 ∨ m = 0 := by
  apply Iff.intro
  · intro g
    cases n
    right; left; rfl
    cases m
    right; right; rfl
    left
    rename_i n m
    have := coprime_of_npow_succ (coprime_of_npow_succ g).symm
    symm; assumption
  · intro h
    rcases h with acob | n_eq_0 | m_eq_zero
    cases n
    rw [npow_zero]
    apply one_gcd
    cases m
    rw [npow_zero]
    apply gcd_one
    rename_i n m
    rw [npow_succ, npow_succ]

    repeat sorry

def dvd_of_coprime_mul : a ∣ b * c -> Coprime a b -> a ∣ c := by
  intro ⟨k, prf⟩  g
  exists k / b
  rw [mul_udiv_assoc, prf, mul_comm]


  sorry

end nat
