
def fact
| 0 => 1
| n + 1 => (n + 1) * fact n
def npr (n r: Nat) := fact n / fact (n - r)

postfix:max "!" => fact

@[simp] def fact_zero : fact 0 = 1 := rfl
@[simp] def fact_succ : fact (n + 1) = (n + 1) * fact n := rfl

def fact_pos (n: Nat) : 0 < fact n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih]

def npr_succ_succ (n m: Nat) : npr (n + 1) (m + 1) = (n + 1) * npr n m := by
  unfold npr
  simp
  rw [Nat.mul_div_assoc]
  induction m with
  | zero => apply Nat.dvd_refl
  | succ m ih =>
    apply Nat.dvd_trans _ ih
    rw [Nat.sub_succ]
    clear ih
    generalize n - m=k; clear n m
    cases k
    apply Nat.dvd_refl
    simp
    apply Nat.dvd_mul_left

def npr_zero_left (n: Nat) : npr 0 n = 1 := by simp [npr]
def npr_zero_right (n: Nat) : npr n 0 = 1 := by simp [npr]; rw [Nat.div_self (fact_pos n)]

def npr_pos (n m: Nat) : 0 < npr n m := by
  induction n generalizing m with
  | zero =>
    rw [npr_zero_left]
    apply Nat.zero_lt_succ
  | succ n ih =>
    cases m with
    | zero =>
      rw [npr_zero_right]
      apply Nat.zero_lt_succ
    | succ m =>
      rw [npr_succ_succ]
      apply Nat.mul_pos
      apply Nat.zero_lt_succ
      apply ih

def fact_dvd_of_le (n m: Nat) : n ≤ m -> fact n ∣ fact m := by
  intro h
  induction m generalizing n with
  | zero =>
    simp at h; subst n
    apply Nat.dvd_refl
  | succ m ih =>
    rw [Nat.le_iff_lt_or_eq] at h
    rcases h with h | h
    rw [Nat.lt_succ] at h
    apply Nat.dvd_trans
    apply ih
    assumption
    apply Nat.dvd_mul_left
    subst n
    apply Nat.dvd_refl
