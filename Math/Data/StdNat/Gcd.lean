import Math.Data.StdNat.Prime
import Math.Data.StdNat.Find

namespace Nat

def dvd_left_of_dvd_of_gcd_eq_one (a b c: Nat) : a ∣ b * c -> a.gcd c = 1 -> a ∣ b := by
  intro dvd gcd_eq
  have p1 := Nat.gcd_mul_dvd_mul_gcd a b c
  rw [gcd_eq, Nat.mul_one] at p1
  have p2 : a.gcd b ∣ a.gcd (b * c) := gcd_dvd_gcd_mul_right_right a b c
  have := Nat.dvd_antisymm p1 p2
  refine gcd_eq_left_iff_dvd.mpr ?_
  rw [←this]
  refine gcd_eq_left_iff_dvd.mp ?_
  assumption

-- a number is atomic if it is irreducible or a unit
-- for Nat this means 1 or Prime
def IsAtomic (n: Nat): Prop := ∀m, m ∣ n -> m = 1 ∨ m = n

def IsPrime (n: Nat): Prop := n ≠ 1 ∧ IsAtomic n

def IsComposite (n: Nat): Prop := ∃a b, a ≠ 1 ∧ b ≠ 1 ∧ n = a * b

def prime2 : IsPrime 2 := by
  apply And.intro
  trivial
  intro n ⟨k, _⟩
  match n with
  | 0 => rw [Nat.zero_mul] at *; contradiction
  | 1 => left; rfl
  | 2 => right; rfl
  | n + 3 =>
    cases k
    rw [Nat.mul_zero] at *; contradiction
    rename_i h
    simp [Nat.mul_add, Nat.add_mul, ←Nat.add_assoc] at h

def notprime0 : ¬IsPrime 0 := by
  intro h
  cases h.right 2 (Nat.dvd_zero _) <;> contradiction
def notprime1 : ¬IsPrime 1 := by
  intro h
  exact h.left rfl
def notcomposite1 : ¬IsComposite 1 := by
  intro ⟨_, _, _, _, eq⟩
  cases Nat.mul_eq_one_iff.mp eq.symm
  contradiction
def not_prime_and_composite (n: Nat) : IsPrime n -> IsComposite n -> False := by
  intro p ⟨n₀, n₁, n₀_ne_1, n₁_ne_1, eq⟩
  subst eq
  cases p.right n₀ (Nat.dvd_mul_right _ _)
  contradiction
  match n₁ with
  | 0 =>
    rw [Nat.mul_zero] at p
    have := notprime0
    contradiction
  | n₁ + 2 =>
    have := Nat.mul_lt_mul_left (a := n₀) (b := 1) (c := n₁ + 2) <| by
      cases n₀
      rw [Nat.zero_mul] at p
      have := notprime0
      contradiction
      apply Nat.zero_lt_succ
    have := this.mpr (Nat.succ_lt_succ (Nat.zero_lt_succ _))
    rename_i h _
    rw [Nat.mul_one, ←h] at this
    exact Nat.lt_irrefl _ this

def prime_gt_one (h: IsPrime n) : 1 < n := by
  have := notprime0
  have := notprime1
  match n with
  | 0 => contradiction
  | n + 2 =>
  apply Nat.succ_lt_succ
  apply Nat.zero_lt_succ

inductive Classify: Nat -> Type where
| unit: Classify 1
| prime: IsPrime n -> Classify n
| composite: IsComposite n -> Classify n

def dvd_le: ∀n m: Nat, n ∣ m -> 0 < m -> n ≤ m := by
  intro n m dvd pos
  obtain ⟨n', eq⟩ := dvd
  subst eq
  apply Nat.le_mul_of_pos_right
  apply Nat.pos_of_mul_pos_left
  assumption

private
abbrev minFac_prop (n x: Nat) := 1 < x ∧ x ∣ n
private
def minFac_prop_exists (n: Nat) (h: n ≠ 1) : ∃x, minFac_prop n x := by
  if n = 0 then
    exists 2
    subst n
    apply And.intro
    trivial
    trivial
  else
    exists n
    apply And.intro
    · match n with
      | n + 2 =>
      apply flip Nat.lt_of_lt_of_le
      apply Nat.le_add_left
      trivial
    apply Nat.dvd_refl

def minFac (n: Nat) :=
  if h:n = 1 then 1 else findP (minFac_prop_exists n h)

def minFac_zero: minFac 0 = 2 := rfl
def minFac_one: minFac 1 = 1 := rfl
def minFac_dvd (n: Nat): minFac n ∣ n := by
  unfold minFac
  split
  apply Nat.one_dvd
  apply (findP_spec (minFac_prop_exists n _)).right
  assumption

def minFact_smallest (n: Nat) (h: 0 < n) : ∀m, 1 < m -> m ∣ n -> minFac n ≤ m := by
  intro m m_pos m_dvd_n
  unfold minFac
  split
  · subst n
    cases Nat.dvd_one.mp m_dvd_n
    apply Nat.le_refl
  · apply Nat.le_of_not_lt
    intro g
    rename_i ne
    cases Or.symm (Decidable.not_and_iff_or_not.mp <| lt_findP_spec (minFac_prop_exists n ne) _ g)
    contradiction
    rename_i g'
    have := Nat.le_of_not_lt g'
    contradiction

def minFac_prime (n: Nat) (h: n ≠ 1): (minFac n).IsPrime := by
  have ⟨find_gt_one, find_dvd⟩ := (findP_spec (minFac_prop_exists n h))
  unfold minFac
  rw [dif_neg h]
  apply And.intro
  intro g
  rw [g] at find_gt_one
  contradiction
  match n with
  | 0 => exact prime2.right
  | n + 2 =>
  intro m m_dvd_find
  have m_dvd_n := Nat.dvd_trans m_dvd_find find_dvd
  match m with
  | 0 =>
    rw [Nat.zero_dvd.mp m_dvd_find] at find_gt_one
    contradiction
  | 1 => left; rfl
  | m + 2 =>
  right
  apply Nat.le_antisymm
  apply dvd_le
  assumption
  apply Nat.lt_trans _ find_gt_one
  trivial
  have := minFact_smallest _ ?_ (m + 2) ?_ m_dvd_n
  unfold minFac at this
  rw [dif_neg h] at this
  assumption
  apply Nat.zero_lt_succ
  apply Nat.succ_lt_succ
  apply Nat.zero_lt_succ

def classify (n: Nat) : Classify n :=
  if h:n = 1 then
    match n with
    | 1 => Classify.unit
  else if g:n.minFac = n then
    Classify.prime <| g ▸ minFac_prime _ h
  else
    Classify.composite <| by
      have minprime := minFac_prime _ h
      have : n.minFac ≠ 0 := by
        intro h
        have := notprime0
        rw [h] at minprime
        contradiction
      exists n.minFac
      exists n / n.minFac
      repeat any_goals apply And.intro
      · have minprime := minFac_prime _ h
        have := minprime.left
        assumption
      · intro div_eq
        apply g
        conv => { rhs; rw [←Nat.div_mul_cancel (minFac_dvd n)] }
        rw [div_eq, Nat.one_mul]
      rw [Nat.mul_div_cancel']
      apply minFac_dvd

instance : Subsingleton (Classify n) where
  allEq := by
    have := notprime1
    have := notcomposite1
    intro a b
    cases a <;> cases b
    any_goals rfl
    any_goals contradiction
    rename_i p c
    have := not_prime_and_composite n p c
    contradiction
    rename_i c p
    have := not_prime_and_composite n p c
    contradiction

def gcd_eq_one_or_dvd_of_prime {p: Nat} (hp: IsPrime p) : ∀n, gcd p n = 1 ∨ p ∣ n := by
  intro n
  apply Decidable.or_iff_not_imp_right.mpr
  intro h
  apply Nat.gcd_eq_iff.mpr
  apply And.intro
  apply Nat.one_dvd
  apply And.intro
  apply Nat.one_dvd
  intro c c_dvd_p c_dvd_n
  cases hp.right _ c_dvd_p
  subst c
  apply Nat.dvd_refl
  subst c
  contradiction

def prime_dvd_mul {p: Nat} (hp: IsPrime p) :
  ∀a b: Nat, p ∣ a * b -> p ∣ a ∨ p ∣ b := by
  intro a b h
  rcases gcd_eq_one_or_dvd_of_prime hp b with ha | dvd
  have := dvd_left_of_dvd_of_gcd_eq_one _ _ _ h ha
  left; assumption
  right; assumption

def prime_factor_pow {p: Nat} (hp: IsPrime p) :
  ∀{a n}, p ∣ a ∧ 0 < n ↔ p ∣ a ^ n := by
  intro a n
  apply Iff.intro
  · intro ⟨⟨k, eq⟩ , pos⟩
    subst a
    rw [Nat.mul_pow]
    apply flip Nat.dvd_trans
    apply Nat.dvd_mul_right
    match n with
    | n + 1 =>
    exists p^n
    rw [Nat.pow_succ']
  · intro dvd
    induction n with
    | zero =>
      obtain ⟨k, an_eq_pk⟩ := dvd
      rw [Nat.pow_zero] at an_eq_pk
      have h := an_eq_pk.symm
      exfalso
      have ⟨_, _⟩  := Nat.mul_eq_one_iff.mp h
      subst p
      exact hp.left rfl
    | succ n ih =>
      apply And.intro _ (Nat.zero_lt_succ _)
      rcases prime_dvd_mul hp _ _ dvd with dvd | dvd
      exact (ih dvd).left
      assumption

def gcd_eq_one_iff_no_common_prime_factor (a b: Nat):
  gcd a b = 1 ↔ ∀k, Nat.IsPrime k -> k ∣ a -> k ∣ b -> False := by
  apply Iff.intro
  intro h k kprime ha hb
  have := Nat.dvd_gcd ha hb
  rw [h] at this
  cases Nat.dvd_one.mp this
  exact kprime.left rfl
  intro nocomm
  apply Decidable.byContradiction
  intro h
  apply nocomm (a.gcd b).minFac (minFac_prime _ h)
  apply Nat.dvd_trans
  apply minFac_dvd
  apply Nat.gcd_dvd_left
  apply Nat.dvd_trans
  apply minFac_dvd
  apply Nat.gcd_dvd_right

def prime_dvd_of_dvd_pow (p a n: Nat) (h: IsPrime p) : p ∣ a ^ n -> p ∣ a := by
  induction n with
  | zero =>
    intro g
    rw [Nat.pow_zero] at g
    cases Nat.dvd_one.mp g
    have := notprime1
    contradiction
  | succ n ih =>
    intro g
    cases gcd_eq_one_or_dvd_of_prime h a <;> rename_i h'
    exact ih <| Nat.dvd_left_of_dvd_of_gcd_eq_one p (a^n) a g h'
    assumption

def pow_gcd_pow (a b n: Nat) : (a ^ n).gcd (b ^ n) = (a.gcd b) ^ n := by
  by_cases h:0 < a
  have ⟨a₀, ha⟩ := Nat.gcd_dvd_left a b
  have ⟨b₀, hb⟩ := Nat.gcd_dvd_right a b
  have gcd_pos := Nat.gcd_pos_of_pos_left b h
  have : gcd a₀ b₀ = 1 := by
    apply Nat.mul_left_cancel gcd_pos
    rw [←Nat.gcd_mul_left, ←ha, ←hb, Nat.mul_one]
  conv => { lhs; rw [ha]; rhs; rw [hb] }
  rw [Nat.mul_pow, Nat.mul_pow, Nat.gcd_mul_left]
  suffices (a₀^n).gcd (b₀^n) = 1 by rw [this, Nat.mul_one]
  · rw [gcd_eq_one_iff_no_common_prime_factor]
    intro k k_prime k_dvd_apow k_dvd_bpow
    have k_dvd_a := prime_dvd_of_dvd_pow _ _ _ k_prime k_dvd_apow
    have k_dvd_b := prime_dvd_of_dvd_pow _ _ _ k_prime k_dvd_bpow
    apply (gcd_eq_one_iff_no_common_prime_factor _ _).mp this
    exact k_prime
    assumption
    assumption
  by_cases hn:0 = n
  subst n
  rw [Nat.pow_zero, Nat.pow_zero, Nat.pow_zero]
  rfl
  cases Nat.le_zero.mp (Nat.le_of_not_lt h)
  rw [Nat.zero_pow, Nat.gcd_zero_left, Nat.gcd_zero_left]
  apply Nat.zero_lt_of_ne_zero; symm; assumption

end Nat
