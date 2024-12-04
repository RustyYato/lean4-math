import Math.Data.Nat.Order

section add

def nat.add_eq_left {a b: nat} : a + b = a -> b = 0 := by
  intro h
  cases b using cases with
  | zero => trivial
  | succ b =>
  have : a < a + b.succ := by
    rw [←add_zero a]
    apply nat.add_lt_add_of_le_of_lt
    rw [add_zero]
    trivial
  rw [h] at this
  have := lt_irrefl this
  contradiction

end add

section dvd

def nat.eq_one_of_mul_eq_left {a b: nat} : a * b = a -> b = 1 ∨ a = 0 := by
  intro h
  if bnz:b = 0 then
    subst b
    rw [mul_zero] at h
    right; symm; assumption
  else if g:b = 1 then
    left; assumption
  else
    right
    have : b = b.pred.pred.succ.succ := by
      cases b using cases
      contradiction
      rename_i b
      cases b using cases
      contradiction
      rename_i b
      rfl
    rw [this] at h
    rw [mul_succ] at h
    cases of_mul_eq_zero (add_eq_left h) <;> trivial

def nat.eq_one_of_mul_eq_right {a b: nat} : a * b = b -> a = 1 ∨ b = 0 := by
  rw [mul_comm]
  apply nat.eq_one_of_mul_eq_left

def nat.dvd (a b: nat) : Prop := ∃k, a * k = b
instance : Dvd nat := ⟨nat.dvd⟩

def nat.dvd_mul_right (a b: nat) : a ∣ a * b := ⟨_, rfl⟩
def nat.dvd_mul_left (a b: nat) : a ∣ b * a := ⟨_, mul_comm _ _⟩
def nat.dvd_trans {a b c: nat} : a ∣ b -> b ∣ c -> a ∣ c
| ⟨ka, ha⟩, ⟨kb, hb⟩ => ⟨ka * kb, by rw [←mul_assoc, ha, hb]⟩
def nat.dvd_antisymm {a b: nat} : a ∣ b -> b ∣ a -> a = b := by
  intro ⟨k₀, ab⟩ ⟨k₁, ba⟩
  subst b
  rw [mul_assoc] at ba
  cases nat.eq_one_of_mul_eq_left ba <;> rename_i h
  cases nat.of_mul_eq_one h
  subst k₀
  rw [mul_one]
  subst a
  rfl

def nat.dvd_zero (a: nat) : a ∣ 0 := ⟨_, mul_zero a⟩
def nat.one_dvd (a: nat) : 1 ∣ a := ⟨_, one_mul a⟩
def nat.le_or_eq_zero_of_dvd {a b: nat} : a ∣ b -> a ≤ b ∨ b = 0 := by
  intro ⟨k, prf⟩
  subst b
  cases k using cases
  rw [mul_zero]
  right; rfl
  left
  rw [mul_succ]
  apply nat.le_add_right
def nat.le_of_dvd_pos {a b: nat} : a ∣ b -> 0 < b -> a ≤ b := by
  intro dvd pos
  cases le_or_eq_zero_of_dvd dvd
  assumption
  subst b
  contradiction

def nat.dvd_add {a b k: nat} : k ∣ a -> k ∣ b -> k ∣ a + b := by
  intro ⟨ka₀, ka⟩ ⟨kb₀, kb⟩
  exists ka₀ + kb₀
  rw [mul_add, ka, kb]

def nat.dvd_sub {a b k: nat} : k ∣ a -> k ∣ b -> k ∣ a - b := by
  intro ⟨ka₀, ka⟩ ⟨kb₀, kb⟩
  exists ka₀ - kb₀
  rw [mul_sub, ka, kb]

def nat.of_dvd_add {a b k: nat} : k ∣ a -> k ∣ a + b -> k ∣ b := by
  intro ⟨ka₀, ka⟩ ⟨kab₀, kab⟩
  exists kab₀ - ka₀
  rw [mul_sub, ka, kab, add_comm, add_sub_cancel]

def nat.zero_dvd {a: nat} : 0 ∣ a ↔ a = 0 := by
  apply Iff.intro
  intro ⟨k, prf⟩
  rw [zero_mul] at prf
  subst a; rfl
  intro h
  subst h
  apply dvd_zero

end dvd
