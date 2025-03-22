
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

def npr_succ_succ (n m: Nat) : (n + 1) * npr n m = npr (n + 1) (m + 1) := by
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
