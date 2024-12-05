import Math.Data.Nat.Prime
import Math.Data.Nat.Gcd
import Math.Data.Multiset.Basic

namespace nat

def product_of : List nat -> nat := List.reduce 1 (· * ·)

def product_of_set : Multiset nat -> nat := by
  apply Quot.lift product_of
  apply List.reduce_spec

def product_of_set_cons : product_of_set (m::ₘ ms) = m * product_of_set ms := by
  quot_ind ms
  rfl

@[simp]
def mk_product_of_set : product_of_set (QuotLike.mk as) = product_of as := rfl
def product_of_set_eq_zero : product_of_set ms = 0 ↔ 0 ∈ ms := by
  quot_ind ms
  simp
  induction ms with
  | nil =>
    apply Iff.intro
    · intro h
      unfold product_of List.reduce at h
      exact (succ_ne_zero 0 h).elim
    · intro
      contradiction
  | cons m ms ih =>
    apply Iff.intro
    intro h
    cases of_mul_eq_zero h
    subst m
    apply List.Mem.head
    apply List.Mem.tail
    apply ih.mp
    assumption
    intro h
    show m * product_of _ = _
    cases h
    rw [zero_mul]
    rename_i h
    rw [ih.mpr h, mul_zero]
def product_of_set_eq_one : product_of_set ms = 1 ↔ ∀x ∈ ms, x = 1 := by
  quot_ind ms
  simp
  induction ms with
  | nil =>
    apply Iff.intro
    · intro h x mem
      contradiction
    · intro
      rfl
  | cons m ms ih =>
    apply Iff.intro
    intro h
    cases of_mul_eq_one h
    clear h; rename_i h
    replace h: product_of ms = 1 := h
    subst m
    intro x mem
    cases mem
    rfl
    apply ih.mp
    assumption
    assumption
    intro h
    show m * product_of ms = 1
    rw [h _ (List.Mem.head _), one_mul, ih.mpr]
    intro x mem
    apply h
    apply List.Mem.tail
    assumption

structure PrimeFactorization (n: nat) where
  ofPrimes ::
  primes: Multiset nat
  spec: ∀x ∈ primes, x.Prime
  product: product_of_set primes = n
  -- prime_counts isn't necessary, but it makes the Subsingleton proof much simpler
  prime_counts: ∀x p, x.Prime -> (primes.MinCount x p ↔ x ^ p ∣ n)

def PrimeFactorization.mk (n: nat) (h: 0 < n) : PrimeFactorization n :=
  if h:n = 1 then PrimeFactorization.ofPrimes ∅ nofun (by subst h; rfl) (by
    intro x p xprime
    subst n
    apply Iff.intro
    intro h
    cases h
    apply one_dvd
    intro h
    cases pow_eq_one.mp (dvd_one.mp h)
    subst x
    contradiction
    subst p
    apply List.MinCount.nil)
  else  by
    have := PrimeFactorization.mk (n /? n.min_fac) (by
      rw [div_of_ge]
      apply zero_lt_succ
      apply dvd.le
      assumption
      apply min_fac_dvd)
    apply PrimeFactorization.ofPrimes (n.min_fac ::ₘ this.primes)
    · intro x mem
      simp at mem
      cases mem
      subst x
      apply min_fac_prime
      assumption
      apply this.spec
      assumption
    · rw [product_of_set_cons, this.product]
      rw [mul_div_of_dvd]
      apply min_fac_dvd
    · intro x p xprime
      conv => {
        rhs
        rw [←mul_div_of_dvd n n.min_fac (by apply min_fac_pos) (by apply min_fac_dvd)]
      }
      apply Iff.intro
      · intro c
        rcases Multiset.of_count_cons c with c | ⟨p_pos, x_eq, c⟩
        have := (this.prime_counts x p xprime).mp c
        apply nat.dvd_trans
        assumption
        apply nat.dvd_mul_left
        subst x
        clear c
        have := (this.prime_counts _ _ xprime).mp c
        cases p
        contradiction
        rw [nat.npow_succ]
        apply mul_left_dvd
        assumption
      · intro h
        if h:x = n.min_fac then
          subst x
          cases p
          apply Multiset.MinCount.zero
          rw [npow_succ] at h
          apply Multiset.MinCount.head
          apply (this.prime_counts _ _ xprime).mpr
          exact of_mul_left_dvd (min_fac_pos _) h
        else
          apply Multiset.MinCount.cons
          apply (this.prime_counts _ _ xprime).mpr
          apply nat.dvd_of_coprime_mul
          assumption
          have : n.min_fac = n.min_fac ^ 1 := by
            show _ = _ ^ (Nat.succ 0)
            rw [npow_succ, npow_zero, mul_one]
          rw [this]
          apply prime_pow_coprime_iff_ne.mpr
          left
          assumption
termination_by n
decreasing_by
  apply div_lt
  assumption
  have := min_fac_prime _ h
  apply Decidable.byContradiction
  intro g
  replace g := le_of_not_lt g
  cases lt_or_eq_of_le g <;> rename_i g
  have : min_fac n ≤ 0 := le_of_lt_succ g
  have := min_fac_pos n
  rw [le_zero _ (le_of_lt_succ g)] at this
  contradiction
  rw [g] at this
  contradiction

def PrimeFactorization.non_zero (p: Nonempty (PrimeFactorization n)) : n ≠ 0 := by
  obtain ⟨p⟩ := p
  intro h
  subst h
  have := p.spec _ (product_of_set_eq_zero.mp p.product)
  contradiction

instance : Inhabited (PrimeFactorization (nat.succ n)) where
  default := PrimeFactorization.mk _ (zero_lt_succ _)

instance : Subsingleton (PrimeFactorization n) where
  allEq := by
    intro a b
    cases a with | ofPrimes as as_primes as_prod as_counts =>
    cases b with | ofPrimes bs bs_primes bs_prod bs_counts =>
    congr
    quot_ind (as bs)
    apply quot.sound
    apply List.MinCount.iff_perm.mpr
    have eqv := fun x p xprime => (as_counts x p xprime).trans (bs_counts x p xprime).symm
    intro x n
    apply Iff.intro
    · intro c
      cases n
      apply List.MinCount.zero
      have := as_primes _ <| List.mem_iff_MinCount_one.mpr <| List.MinCount.reduce c (m := 1) (Nat.succ_le_succ (Nat.zero_le _))
      exact (eqv x _ this).mp c
    · intro c
      cases n
      apply List.MinCount.zero
      have := bs_primes _ <| List.mem_iff_MinCount_one.mpr <| List.MinCount.reduce c (m := 1) (Nat.succ_le_succ (Nat.zero_le _))
      exact (eqv x _ this).mpr c

instance : DecidableEq (PrimeFactorization n) := by
  intro a b
  apply Decidable.isTrue
  apply Subsingleton.allEq

end nat
