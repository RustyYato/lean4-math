import Math.Data.Nat.Dvd
import Math.Data.Nat.Find

namespace nat

-- a is prime if
-- * the only divisors of a are 1 or itself
-- * a is not a unit
def Prime (a: nat) : Prop := a ≠ 1 ∧ ∀b, b ∣ a -> b = 1 ∨ b = a

-- a is composite if there exists a non-trival divisor of it
def Composite (a: nat): Prop := ∃x, x ∣ a ∧ x ≠ 1 ∧ x ≠ a

def Composite.ne_one : Composite a -> a ≠ 1 := by
  intro one_comp h
  subst h
  have ⟨k, ⟨k₀, k₀_eq⟩ , k_ne, _⟩ := one_comp
  have ⟨_, _⟩  := of_mul_eq_one k₀_eq
  contradiction

inductive Classify : nat -> Type where
| Unit : a = 1 -> Classify a
| Prime : Prime a -> Classify a
| Composite : Composite a -> Classify a

def not_prime_and_composite : Prime a -> Composite a -> False := by
  intro ⟨ne_one, p⟩ ⟨k, k_dvd_a, k_ne_one, k_ne_a⟩
  cases p _ k_dvd_a <;> contradiction

instance : Subsingleton (Classify x) where
  allEq := by
    intro a b
    cases a <;> cases b
    any_goals rfl
    any_goals
      rename x = 1 => hx
      cases hx
    any_goals
      rename Prime 1 => one_prime
      have := one_prime.left
      contradiction
    any_goals
      rename Composite 1 => one_comp
      have := one_comp.ne_one
      contradiction
    all_goals
      exfalso
      apply not_prime_and_composite <;> assumption

instance : Inhabited (Classify n) where
  default := by
    if h₀:n = 0 then
      apply Classify.Composite
      subst n
      exists 10
    else if h:n = 1 then
      apply Classify.Unit
      assumption
    else if g:∃x < n, x ∣ n ∧ x ≠ 1 ∧ x ≠ n then
      apply Classify.Composite
      obtain ⟨x, _, _, _, _⟩ := g
      exists x
    else
      apply Classify.Prime
      replace g := not_exists.mp g
      apply And.intro h
      intro b b_dvd_n
      have npos : 0 < n := lt_of_le_of_ne (zero_le _) (Ne.symm h₀)
      cases lt_or_eq_of_le (dvd.le npos b_dvd_n)
      rename_i h
      have := not_and.mp (not_and.mp (g b) h) b_dvd_n
      apply Decidable.or_iff_not_and_not.mpr
      exact not_and.mp (not_and.mp (g b) h) b_dvd_n
      subst n; right; rfl

def Classify.intro n : Classify n := default

instance : Decidable (Prime n) :=
  match Classify.intro n with
  | .Prime h => .isTrue h
  | .Unit h => .isFalse fun g => g.left h
  | .Composite h => .isFalse fun g => not_prime_and_composite g h

instance : Decidable (Composite n) :=
  match Classify.intro n with
  | .Composite h => .isTrue h
  | .Unit h => .isFalse fun g => g.ne_one h
  | .Prime h => .isFalse fun g => not_prime_and_composite h g

def prime_2 : Prime 2 := by decide
def prime_3 : Prime 3 := by decide
def prime_5 : Prime 5 := by decide

def exists_min_fac (n: nat) : ∃x > 0, x ∣ n ∧ (x = 1 ↔ n = 1) := by
  cases n using cases with
  | zero => exists 2
  | succ n => exists n.succ

def min_fac (n: nat) : nat := findP (exists_min_fac n)
def min_fac_dvd (n: nat) : min_fac n ∣ n := by
  have ⟨_, _, _⟩  := findP_spec (exists_min_fac n)
  assumption
def min_fac_prime (n: nat) (h: n ≠ 1) : (min_fac n).Prime := by
  have ⟨min_fac_pos, _, min_fac_eq_one_iff⟩  := findP_spec (exists_min_fac n)
  apply And.intro
  intro g
  have min_fac_eq_one_iff : min_fac n = 1 ↔  n = 1 := min_fac_eq_one_iff
  rw [g] at min_fac_eq_one_iff
  have := min_fac_eq_one_iff.mp rfl
  contradiction
  intro x x_dvd_min_fac
  cases lt_or_eq_of_le <| nat.dvd.le (min_fac_pos) x_dvd_min_fac
  rename_i x_lt_min_fac
  if xpos:0 < x then
    have := not_and.mp (not_and.mp (lt_findP_spec (exists_min_fac n) _ x_lt_min_fac) xpos) (
      nat.dvd_trans x_dvd_min_fac (min_fac_dvd n)
    )
    rw [Iff.comm] at this
    cases (Decidable.not_iff.mp this).mp h
    left; rfl
  else
    cases (le_zero _ (le_of_not_lt xpos))
    have := nat.zero_dvd.mp x_dvd_min_fac
    replace min_fac_pos : 0 < min_fac n := min_fac_pos
    rw [this] at min_fac_pos
    contradiction
  subst x
  right
  rfl

end nat
