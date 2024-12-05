import Math.Data.Nat.Order
import Math.Data.Nat.Find

namespace nat

section add

def add_eq_left {a b: nat} : a + b = a -> b = 0 := by
  intro h
  cases b using cases with
  | zero => trivial
  | succ b =>
  have : a < a + b.succ := by
    rw [←add_zero a]
    apply add_lt_add_of_le_of_lt
    rw [add_zero]
    trivial
  rw [h] at this
  have := lt_irrefl this
  contradiction

end add

section dvd

def eq_one_of_mul_eq_left {a b: nat} : a * b = a -> b = 1 ∨ a = 0 := by
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

def eq_one_of_mul_eq_right {a b: nat} : a * b = b -> a = 1 ∨ b = 0 := by
  rw [mul_comm]
  apply eq_one_of_mul_eq_left

def dvd (a b: nat) : Prop := ∃k, a * k = b
instance : Dvd nat := ⟨dvd⟩

def dvd_mul_right (a b: nat) : a ∣ a * b := ⟨_, rfl⟩
def dvd_mul_left (a b: nat) : a ∣ b * a := ⟨_, mul_comm _ _⟩
def dvd_trans {a b c: nat} : a ∣ b -> b ∣ c -> a ∣ c
| ⟨ka, ha⟩, ⟨kb, hb⟩ => ⟨ka * kb, by rw [←mul_assoc, ha, hb]⟩
def dvd_antisymm {a b: nat} : a ∣ b -> b ∣ a -> a = b := by
  intro ⟨k₀, ab⟩ ⟨k₁, ba⟩
  subst b
  rw [mul_assoc] at ba
  cases eq_one_of_mul_eq_left ba <;> rename_i h
  cases of_mul_eq_one h
  subst k₀
  rw [mul_one]
  subst a
  rfl

def dvd_zero (a: nat) : a ∣ 0 := ⟨_, mul_zero a⟩
def one_dvd (a: nat) : 1 ∣ a := ⟨_, one_mul a⟩
def le_or_eq_zero_of_dvd {a b: nat} : a ∣ b -> a ≤ b ∨ b = 0 := by
  intro ⟨k, prf⟩
  subst b
  cases k using cases
  rw [mul_zero]
  right; rfl
  left
  rw [mul_succ]
  apply le_add_right
def le_of_dvd_pos {a b: nat} : a ∣ b -> 0 < b -> a ≤ b := by
  intro dvd pos
  cases le_or_eq_zero_of_dvd dvd
  assumption
  subst b
  contradiction

def dvd_add {a b k: nat} : k ∣ a -> k ∣ b -> k ∣ a + b := by
  intro ⟨ka₀, ka⟩ ⟨kb₀, kb⟩
  exists ka₀ + kb₀
  rw [mul_add, ka, kb]

def dvd_sub {a b k: nat} : k ∣ a -> k ∣ b -> k ∣ a - b := by
  intro ⟨ka₀, ka⟩ ⟨kb₀, kb⟩
  exists ka₀ - kb₀
  rw [mul_sub, ka, kb]

def of_dvd_add {a b k: nat} : k ∣ a -> k ∣ a + b -> k ∣ b := by
  intro ⟨ka₀, ka⟩ ⟨kab₀, kab⟩
  exists kab₀ - ka₀
  rw [mul_sub, ka, kab, add_comm, add_sub_cancel]

@[refl]
def dvd_refl (n: nat) : n ∣ n := ⟨1, one_mul _⟩

def zero_dvd {a: nat} : 0 ∣ a ↔ a = 0 := by
  apply Iff.intro
  intro ⟨k, prf⟩
  rw [zero_mul] at prf
  subst a; rfl
  intro h
  subst h
  apply dvd_zero

def dvd.le {a b: nat} (h: 0 < a) : b ∣ a -> b ≤ a := by
  intro ⟨x, eq⟩
  subst a
  cases x using cases
  rw [mul_zero] at h
  contradiction
  rw [mul_succ]
  apply le_add_right

instance (a b: nat) : Decidable (a ∣ b) :=
  if h₀:b = 0 then
    .isTrue (by
      subst b
      apply dvd_zero)
  else if h₁:a = 1 then
    .isTrue (by
      subst h₁
      apply one_dvd)
  else if h₂:∃x < b, a * x = b then
    .isTrue <| by
      obtain ⟨x, x_lt_b, ax_eq_b⟩ := h₂
      exists x
  else
    .isFalse <| by
      intro ⟨x, prf⟩
      subst b
      have := (h₂ ⟨ x, ·, rfl⟩)
      cases x using cases with
      | zero =>
        rw [mul_zero] at h₀
        contradiction
      | succ x =>
      cases a using cases with
      | zero =>
        rw [zero_mul] at h₀
        contradiction
      | succ a =>
        apply this; clear this
        rw [succ_mul, mul_succ]
        conv => { lhs; rw [←add_zero x.succ] }
        apply lt_add_left_iff_lt.mp
        apply add_pos
        left
        cases a using cases
        contradiction
        apply zero_lt_succ

def dvd_one {a: nat} : a ∣ 1 ↔ a = 1 := by
  apply flip Iff.intro
  intro h; subst h
  rfl
  intro ⟨k, prf⟩
  exact (of_mul_eq_one prf).left

def mul_left_dvd {a b k: nat} : a ∣ b -> k * a ∣ k * b := by
  intro ⟨x, h⟩
  exists x
  rw [mul_assoc, h]

def of_mul_left_dvd {a b k: nat} (h: 0 < k) : k * a ∣ k * b -> a ∣ b := by
  intro ⟨x, g⟩
  exists x
  rw [mul_assoc] at g
  exact (mul_left_cancel_iff h).mp g

def dvd_pow_succ (a: nat) (n: Nat) : a ∣ a ^ (n + 1) := ⟨a ^ n, (npow_succ _ _).symm⟩

def dvd_pow_le (a: nat) (n m: Nat) : m ≤ n -> a ^ m ∣ a ^ n := by
  intro le
  exists a ^ (n - m)
  rw [pow_mul, Nat.add_sub_cancel']
  assumption

def mul_dvd_mul (a b k: nat) : a ∣ b -> a * k ∣ b * k := by
  intro ⟨x, prf⟩
  exists x
  rw [mul_right_comm, prf]

end dvd

end nat
