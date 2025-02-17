namespace Int

def cases {motive: Int -> Sort _}
  (zero: motive 0) (pos: ∀n: Nat, motive ↑(n + 1)) (neg: ∀n: Nat, motive -[n+1]) : ∀i, motive i
| 0 => zero
| .negSucc _ => neg _
| .ofNat (.succ _) => pos _

def coe_cases {motive: Int -> Sort _}
  (ofNat: ∀n: Nat, motive n)
  (negSucc: ∀n: Nat, motive (Int.negSucc n)): ∀x, motive x
| .negSucc _ => negSucc _
| .ofNat _ => ofNat _

def induction {motive : Int → Prop} (i : Int)
  (zero : motive 0) (succ : ∀i, motive i → motive (i + 1)) (pred : ∀i, motive i → motive (i - 1)) : motive i := by
induction i with
| ofNat i =>
  induction i with
  | zero => exact zero
  | succ i ih => exact succ _ ih
| negSucc i =>
  induction i with
  | zero =>
    suffices motive (0 - 1) from this
    apply pred
    assumption
  | succ n ih =>
    suffices motive (-[n+1] - 1) from this
    apply pred
    assumption

def natAbs_npow (a: Int) (n: Nat) : (a ^ n).natAbs = a.natAbs ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Int.pow_succ, Nat.pow_succ, Int.natAbs_mul, ih]

def ofNat_npow (a: Nat) (n: Nat) : ((a ^ n: Nat): Int) = (a: Int) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Int.pow_succ, Nat.pow_succ, Int.ofNat_mul, ih]

def mul_pow (a b: Int) (n: Nat) : a ^ n * b ^ n = (a * b) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Int.pow_succ, Int.pow_succ, Int.pow_succ, ←ih]
    ac_rfl

def emod_two_eq_zero_or_one (n : Int) : n % 2 = 0 ∨ n % 2 = 1 :=
  have h : n % 2 < 2 :=  by omega
  have h₁ : 0 ≤ n % 2 := Int.emod_nonneg _ (by decide)
  match n % 2, h, h₁ with
  | (0 : Nat), _ ,_ => Or.inl rfl
  | (1 : Nat), _ ,_ => Or.inr rfl
  | (k + 2 : Nat), h₁, _ => by omega
  | -[a+1], _, h₁ => by cases h₁

def of_toNat_eq_zero (a: Int) : a.toNat = 0 -> a ≤ 0 := by
  intro h
  cases a with
  | ofNat a =>
    cases a
    apply Int.le_refl
    contradiction
  | negSucc a =>
    exact negSucc_le_zero a

def pos_of_sign_pos (a: Int) : 0 < a.sign -> 0 < a := by
  intro
  cases a using Int.cases
  contradiction
  exact ofNat_succ_pos _
  contradiction

def pow_ofNat (a n: Nat) : (a ^ n: Nat) = (a: Int) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Int.pow_succ, Nat.pow_succ, Int.ofNat_mul, ih]

end Int
