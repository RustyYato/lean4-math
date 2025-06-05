import Math.Data.Multiset.Algebra
import Math.Data.Nat.Gcd
import Math.Order.Defs

namespace Nat

structure Factorization (n: ℕ) where
  ofFactors ::
  toFactors: Multiset ℕ
  product_eq: toFactors.prod = n
  no_ones: 1 ∉ toFactors
  zero_eq : n = 0 -> toFactors = 0::ₘ∅

private def factorizationFast' (n: ℕ) : Array ℕ :=
  if n = 0 then #[0] else Id.run do
  let mut n := n
  let mut out : Array ℕ := #[]

  while 2 ∣ n do
    out := out.push 2
    n := n / 2
  while 3 ∣ n do
    out := out.push 3
    n := n / 3

  let mut i := 5

  -- each step through the loop we increment by 6
  -- since we already checked 2 and 3, we only need
  -- to check numbers of the form 6 n + 1 and 6 n + 5
  -- since all other numbers are composite
  -- and we only need to check primes for the factorization
  while i ≤ n do
    while i ∣ n do
      out := out.push i
      n := n / i
    i := i + 2
    while i ∣ n do
      out := out.push i
      n := n / i
    i := i + 4

  return out

def factorizationFast (n: ℕ) : Multiset ℕ :=
  Multiset.mk (factorizationFast' n).toList

private def factorizationRec
  {motive: ∀n i: ℕ, n ≠ 0 -> 1 < i -> Sort*}
  (base: ∀n i h₀ h₁, n < i -> motive n i h₀ h₁)
  (dvd: ∀n i h₀ h₁ (h: i ∣ n), i ≤ n -> motive (n / i) i (by
    intro g
    rw [Nat.div_eq_zero_iff] at g
    rcases g with rfl | g
    contradiction
    have := Nat.le_of_dvd (Nat.zero_lt_of_ne_zero h₀) h
    rw [←Nat.not_le] at g
    contradiction) h₁ -> motive n i h₀ h₁)
  (succ: ∀n i h₀ h₁ (h: ¬i ∣ n), i ≤ n -> motive n (i + 1) h₀ (by omega) -> motive n i h₀ h₁)
  (n: ℕ) (i: ℕ)
  (hn: n ≠ 0) (hi: 1 < i)
  : motive n i hn hi :=
  if h₀:n < i then
    base n i hn hi h₀
  else if h₁:i ∣ n then
    dvd n i hn hi h₁ (by omega) (factorizationRec base dvd succ _ _ _ _)
  else
    succ n i hn hi h₁ (by omega) (factorizationRec base dvd succ _ _ _ _)
termination_by (n, n - i)
decreasing_by
  · apply Prod.Lex.left
    refine div_lt_self ?_ hi
    omega
  · apply Prod.Lex.right
    match n with
    | n + 1 =>
    simp
    rw [Nat.succ_sub]
    apply Nat.lt_succ_self
    simp at h₀
    rw [Nat.le_iff_lt_or_eq] at h₀
    rcases h₀ with h₀ | rfl
    omega
    exfalso
    apply h₁
    apply Nat.dvd_refl

private def factorization'
  (n: ℕ) (i: ℕ)
  (hn: n ≠ 0) (hi₀: 1 < i)
  (output: Multiset ℕ)
  : Multiset ℕ :=
  if h₀:n < i then
    output
  else if h:i ∣ n then
    factorization' (n / i) i (by
      obtain ⟨k, rfl⟩ := h
      intro h
      apply hn
      simp at h
      rcases h with rfl | h
      simp
      cases k
      simp
      rw [←Nat.not_le] at h
      exfalso; apply h
      refine Nat.le_mul_of_pos_right i ?_
      apply Nat.zero_lt_succ) hi₀ (i::ₘoutput)
  else
    factorization' n (i + 1) hn (Nat.lt_trans hi₀ (Nat.lt_succ_self _)) output
termination_by (n, n - i)
decreasing_by
  · apply Prod.Lex.left
    refine div_lt_self ?_ hi₀
    omega
  · apply Prod.Lex.right
    match n with
    | n + 1 =>
    simp
    rw [Nat.succ_sub]
    apply Nat.lt_succ_self
    simp at h₀
    rw [Nat.le_iff_lt_or_eq] at h₀
    rcases h₀ with h₀ | rfl
    omega
    exfalso
    apply h
    apply Nat.dvd_refl

-- @[implemented_by factorizationFast]
def factorization (n: ℕ) : Multiset ℕ :=
  if h:n = 0 then
    Multiset.mk [0]
  else
    factorization' n 2 h (Nat.lt_succ_self _) ∅

def factorization'_output
  (n: ℕ) (i: ℕ)
  (hn: n ≠ 0) (hi₀: 1 < i)
  (output: Multiset ℕ)
  : factorization' n i hn hi₀ output = factorization' n i hn hi₀ ∅ ++ output := by
  induction n, i, hn, hi₀ using factorizationRec generalizing output with
  | base _ _ _ _ h =>
    unfold Nat.factorization'
    simp [h]
  | dvd n i hn hi i_dvd_n h ih =>
    unfold Nat.factorization'
    simp [i_dvd_n, Nat.not_lt.mpr h]
    rw [ih, ih (i::ₘ_), Multiset.append_assoc]
    simp
  | succ n i hn hi h g ih =>
    unfold Nat.factorization'
    simp [h, Nat.not_lt.mpr g]
    rw [ih]

def factorization'_prod_eq_one_iff
  (n: ℕ) (i: ℕ)
  (hn: n ≠ 0) (hi₀: 1 < i)
  : (factorization' n i hn hi₀ ∅).prod = 1 ↔ n < i := by
  induction n, i, hn, hi₀ using factorizationRec with
  | base n i hn hi h =>
    unfold factorization'
    simp [h]
  | dvd n i hn hi h g ih =>
    unfold factorization'
    simp [h, Nat.not_lt.mpr g]
    rw [factorization'_output, Multiset.prod_append]
    simp
    intro h₀
    rw [Nat.mul_eq_one_iff] at h₀
    obtain ⟨h₀, rfl⟩ := h₀
    rw [ih] at h₀
    simp at h₀
    subst n
    contradiction
  | succ n i hn hi h g ih =>
    unfold factorization'
    simp [h, Nat.not_lt.mpr g]
    rw [ih]
    rw [Nat.not_lt]
    rw [Nat.le_iff_lt_or_eq] at g
    cases g
    omega
    subst n
    exfalso; apply h
    apply Nat.dvd_refl

def no_smaller_factor (n i: ℕ) := ∀x < i, x ∣ n -> x = 1

def no_smaller_factor.init (h: n ≠ 0) : no_smaller_factor n 2 := by
  intro x hx dvd
  match x with
  | 1 => rfl
  | 0 =>
  rw [Nat.zero_dvd] at dvd
  subst n; contradiction

def no_smaller_factor.base (h: no_smaller_factor n i) (g: n < i) : n = 1 := by
  apply h
  assumption
  apply Nat.dvd_refl

def no_smaller_factor.succ (h: no_smaller_factor n i) (g: ¬i ∣ n) : no_smaller_factor n (i + 1) := by
  intro x hx _
  rw [Nat.lt_succ, Nat.le_iff_lt_or_eq] at hx
  rcases hx with hx | rfl
  · apply h
    assumption
    assumption
  · contradiction

def no_smaller_factor.dvd (h: no_smaller_factor n i) (g: i ∣ n) : no_smaller_factor (n / i) i := by
  intros x hx _
  apply h
  assumption
  rw [←Nat.mul_div_cancel' g]
  apply Nat.dvd_trans
  assumption
  apply Nat.dvd_mul_left

def factorization'_prod_eq
  (n: ℕ) (i: ℕ)
  (hn: n ≠ 0) (hi₀: 1 < i)
  (hi₁: ∀x < i, x ∣ n -> x = 1)
  : (factorization' n i hn hi₀ ∅).prod = n := by
  induction n, i, hn, hi₀ using factorizationRec with
  | base _ _ _ _ h =>
    unfold Nat.factorization'
    simp [h]
    symm
    apply no_smaller_factor.base
    apply hi₁
    assumption
  | succ n i hn hi h g ih =>
    unfold Nat.factorization'
    simp [h, Nat.not_lt.mpr g]
    rw [ih]
    apply no_smaller_factor.succ
    assumption
    assumption
  | dvd n i hn hi i_dvd_n h ih =>
    unfold Nat.factorization'
    simp [i_dvd_n, Nat.not_lt.mpr h]
    rw [factorization'_output, Multiset.prod_append]
    rw [ih]
    simp
    rw [Nat.div_mul_cancel]
    assumption
    apply no_smaller_factor.dvd
    assumption
    assumption

def factorization'_no_ones
  (n: ℕ) (hn: n ≠ 0)
  (i: ℕ) (hi₀: 1 < i)
  (output: Multiset ℕ)
  (hout: 1 ∉ output) : 1 ∉ factorization' n i hn hi₀ output := by
  induction n, i, hn, hi₀, output using factorization'.induct with
  | case1 n hn i hi₀ output h => simpa [h, Nat.factorization']
  | case2 n hn i hi₀ out h g ih =>
    unfold Nat.factorization'
    simp [h, g]
    apply ih
    simp
    apply And.intro
    omega
    assumption
  | case3 n hn i hi₀ out h g ih =>
    unfold Nat.factorization'
    simp [h, g]
    apply ih
    assumption

def factorization'_primes
  (n: ℕ) (i: ℕ)
  (hn: n ≠ 0) (hi: 1 < i)
  (hi': ∀x < i, x ∣ n -> x = 1) : ∀p ∈ factorization' n i hn hi ∅, p.IsPrime := by
  intro p hp
  induction n, i, hn, hi using factorizationRec with
  | base _ _ _ _ h =>
    unfold Nat.factorization' at hp
    simp [h] at hp
    contradiction
  | succ n i hn hi h g ih =>
    unfold Nat.factorization' at hp
    simp [h, Nat.not_lt.mpr g] at hp
    apply ih
    · apply no_smaller_factor.succ
      assumption
      assumption
    · assumption
  | dvd n i hn hi h g ih =>
    unfold Nat.factorization' at hp
    simp [h, Nat.not_lt.mpr g] at hp
    rw [Nat.factorization'_output, Multiset.append_comm, Multiset.cons_append,
      Multiset.nil_append] at hp
    simp at hp
    rcases hp with rfl | hp
    · apply And.intro
      omega
      intro x hx
      rcases Nat.lt_or_eq_of_le (Nat.le_of_dvd (by omega) hx)
      left; apply hi'
      assumption
      apply Nat.dvd_trans
      assumption
      assumption
      right; assumption
    · apply ih
      apply no_smaller_factor.dvd
      repeat assumption

def factorization_primes (n: ℕ) (hn: 0 < n) : ∀p ∈ factorization n, p.IsPrime := by
  intro p hp
  refine factorization'_primes n 2 (by omega) (by omega) ?_ ?_ ?_
  · apply no_smaller_factor.init
    omega
  · unfold factorization at hp
    rw [dif_neg] at hp
    assumption

instance : Top (Factorization n) where
  top := {
    toFactors := factorization n
    product_eq := by
      unfold factorization
      split
      subst n
      simp
      rfl
      rw [factorization'_prod_eq]
      apply no_smaller_factor.init
      assumption
    no_ones := by
      unfold factorization
      split
      subst n
      simp
      rename_i h
      apply factorization'_no_ones
      intro; contradiction
    zero_eq := by
      rintro rfl
      rfl
  }

def prod_eq_one (m: Multiset ℕ) : m.prod = 1 ↔ ∀x ∈ m, x = 1 := by
  apply Iff.intro
  · intro h x hx
    induction m with
    | nil => contradiction
    | cons a as ih =>
      simp at hx
      simp at h
      rw [Nat.mul_eq_one_iff] at h
      obtain ⟨rfl, h⟩ := h
      · rcases hx with rfl | hx
        rfl
        apply ih
        assumption
        assumption
  · intro h
    apply Multiset.prod_eq_one
    assumption


instance : Subsingleton (Factorization 0) where
  allEq := by
    intro ⟨a, ha₀, ha₁, ha₂⟩ ⟨b, hb₀, hb₁, hb₂⟩
    congr
    rw [ha₂ rfl, hb₂ rfl]
instance : Subsingleton (Factorization 1) where
  allEq := by
    intro ⟨a, ha₀, ha₁, ha₂⟩ ⟨b, hb₀, hb₁, hb₂⟩
    congr
    clear ha₂ hb₂
    ext
    induction a generalizing b with
    | nil =>
      induction b with
      | nil => simp
      | cons b bs ih =>
        simp [Nat.mul_eq_one_iff] at hb₀
        obtain ⟨rfl, _⟩ := hb₀
        exfalso; apply hb₁
        simp
    | cons a as ih =>
      simp [Nat.mul_eq_one_iff] at ha₀
      obtain ⟨rfl, _⟩ := ha₀
      exfalso; apply ha₁
      simp
instance [Nat.IsPrimeClass n] : Subsingleton (Factorization n) where
  allEq := by
    suffices ∀a: Factorization n, a.toFactors = n::ₘ∅ by
      intro a b
      have ha := this a
      have hb := this b
      cases a ; cases b
      congr
      simp at ha hb
      rw [ha, hb]
    intro ⟨a, ha₀, ha₁, ha₂⟩
    simp
    induction a with
    | nil =>
      simp at ha₀
      subst n
      contradiction
    | cons a as ih =>
      clear ih
      simp at ha₀
      rcases Nat.prime_dvd_mul (Nat.prime n) a as.prod (ha₀ ▸ Nat.dvd_refl n) with h | h
      · obtain ⟨k, rfl⟩ := h
        rw [Nat.mul_assoc, Nat.mul_eq_left, Nat.mul_eq_one_iff] at ha₀
        obtain ⟨rfl, ha₀⟩ := ha₀
        simp
        congr
        suffices ∀x, x ∉ as by
          induction as
          rfl
          rename_i a _ _
          have := this a (by simp)
          contradiction
        rw [prod_eq_one] at ha₀
        simp at ha₁
        cases ha₁
        intro x hx
        have := ha₀ x hx
        subst x
        contradiction
        rintro rfl
        contradiction
      · obtain ⟨k, eq⟩ := h
        rw [eq] at ha₀
        rw [show (a * (n * k) = n * (a * k)) by ac_rfl, Nat.mul_eq_left, Nat.mul_eq_one_iff] at ha₀
        obtain ⟨rfl, rfl⟩ := ha₀
        simp at ha₁
        rintro rfl
        contradiction

-- a factorization a ≤ b iff it every factor in b can be partitioned into
-- sets of factors which corrospond one-to-one with factors in a
-- for example 15 * 8 ≤ 3 * 5 * 2 * 4 becuase 15 = 3 * 5 and 8 = 2 * 4
protected inductive Factorization.LE : Multiset ℕ -> Multiset ℕ -> Prop where
| nil : Factorization.LE ∅ ∅
| cons (a: ℕ) (b: Multiset ℕ) (as bs: Multiset ℕ) :
  a = b.prod ->
  Factorization.LE as bs ->
  Factorization.LE (a::ₘas) (b ++ bs)

instance : LE (Factorization n) where
  le a b := Factorization.LE a.toFactors b.toFactors
instance : LT (Factorization n) where
  lt a b := (a ≤ b) ∧ ¬(b ≤ a)

def Factorization.LE.nil_iff : Factorization.LE ∅ as ↔ as = ∅ := by
  apply flip Iff.intro
  rintro rfl
  apply Factorization.LE.nil
  intro h
  revert h
  generalize hb:(∅: Multiset ℕ) = b
  intro h
  cases h
  rfl
  have := Multiset.nil_ne_cons hb
  contradiction

def Factorization.LE.cons_iff : Factorization.LE (a::ₘas) c ↔ ∃c₀ c₁, c = c₀ ++ c₁ ∧ Factorization.LE as c₁ ∧ a = c₀.prod := by
  apply flip Iff.intro
  · rintro ⟨c₀, c₁, rfl, h, g⟩
    apply Factorization.LE.cons
    assumption
    assumption
  generalize ha':a::ₘas = a'
  intro h
  induction h generalizing as with
  | nil =>
    have := Multiset.nil_ne_cons ha'.symm
    contradiction
  | cons a₀ b as₀ bs h g ih =>
    have : a₀ ∈ a₀::ₘas₀ := by simp
    rw [←ha'] at this; simp at this
    rw [Multiset.mem_spec] at this
    rcases this with rfl | ⟨as, rfl⟩
    · rw [Multiset.cons_inv] at ha'
      subst as₀
      exists b
      exists bs
    · rw [Multiset.cons_comm, Multiset.cons_inv] at ha'
      have ⟨c₀, c₁, h₀, h₁, h₂⟩ := ih ha'
      exists c₀
      exists b ++ c₁
      apply And.intro
      rw [h₀]
      ac_rfl
      apply And.intro
      apply Factorization.LE.cons
      repeat assumption

def Factorization.LE.spec : Factorization.LE as bs ↔ ∃(partitions: Multiset (Multiset ℕ)), as = partitions.map Multiset.prod ∧ bs = partitions.flatten := by
  induction as generalizing bs with
  | nil =>
    simp [nil_iff]
    apply Iff.intro
    rintro rfl
    exact ⟨∅, rfl, rfl⟩
    rintro ⟨paritions, eq_nil, rfl⟩
    rw [Eq.comm, Multiset.map_eq_empty] at eq_nil
    subst paritions
    rfl
  | cons a as ih =>
    apply Iff.intro
    · rw [cons_iff]
      rintro ⟨b, bs, rfl, g, rfl⟩
      rw [ih] at g
      obtain ⟨paritions, rfl, rfl⟩ := g
      clear ih
      refine ⟨b::ₘparitions, ?_, ?_⟩
      · simp
      · rw [Multiset.flatten_cons]
    · rintro ⟨paritions, ha, rfl⟩
      rw [Eq.comm, Multiset.map_eq_cons] at ha
      obtain ⟨p, ps, rfl, _, _⟩ := ha
      rw [Multiset.flatten_cons]
      apply Factorization.LE.cons
      assumption
      rw [ih]
      exists ps

def Factorization.LE.of_append :
  Factorization.LE (a ++ b) c -> ∃c₀ c₁, c = c₀ ++ c₁ ∧ Factorization.LE b c₁ ∧ a.prod = c₀.prod := by
  intro h
  induction a generalizing b c with
  | nil =>
    refine ⟨∅, c, ?_, ?_, ?_⟩
    simp
    simpa using h
    rfl
  | cons a as ih =>
    simp [cons_iff] at h
    obtain ⟨c₀, c₁, rfl, le, a_eq⟩ := h
    obtain ⟨c₂, c₃, rfl, _, _⟩ := ih le
    refine ⟨c₀ ++ c₂, c₃, ?_, ?_, ?_⟩
    ac_rfl
    assumption
    simp [Multiset.prod_append]
    congr

instance : IsPreOrder (Factorization n) where
  le_refl a := by
    obtain ⟨a, h₀, h₁, h₂⟩ := a
    show Factorization.LE _ _
    simp
    clear h₀ h₁ h₂
    induction a with
    | nil => apply Factorization.LE.nil
    | cons a as ih =>
      rw (occs := [2]) [←Multiset.nil_append as]
      rw [←Multiset.cons_append]
      apply Factorization.LE.cons
      simp
      assumption
  le_trans := by
    intro ⟨a, ha₀, ha₁, ha₂⟩ ⟨b, hb₀, hb₁, hb₂⟩ ⟨c, hc₀, hc₁, hc₂⟩ h g
    replace h : Factorization.LE a b := h
    replace g : Factorization.LE b c := g
    show Factorization.LE a c
    clear ha₀ ha₁ ha₂
    clear hb₀ hb₁ hb₂
    clear hc₀ hc₁ hc₂
    induction h generalizing c with
    | nil => assumption
    | cons a b as bs a_eq_bprod as_le_bs ih =>
      obtain ⟨k₀, k₁, rfl, le, prod_eq⟩  := Factorization.LE.of_append g
      clear g
      replace ih := ih _ le
      apply Factorization.LE.cons
      rwa [a_eq_bprod]
      assumption

end Nat
