import Math.Function.Basic
import Math.Type.Basic

-- use a different namespace so that
def nat := Nat

instance : Repr nat := instReprNat

def nat.toNat : nat -> Nat := id
def nat.ofNat : Nat -> nat := id

@[simp]
def nat.ofNat.LeftInverse : ∀x, nat.ofNat (nat.toNat x) = x := fun _ => rfl
@[simp]
def nat.toNat.LeftInverse : ∀x, nat.toNat (nat.ofNat x) = x := fun _ => rfl

instance : OfNat nat n := ⟨n⟩

def nat.zero : nat := 0
def nat.succ : nat -> nat := Nat.succ

@[simp]
def nat.ofNat_zero : nat.ofNat 0 = 0 := rfl
@[simp]
def nat.ofNat_succ : nat.ofNat (Nat.succ n) = (nat.ofNat n).succ := rfl
@[simp]
def nat.toNat_zero : nat.toNat 0 = 0 := rfl
@[simp]
def nat.toNat_succ : nat.toNat (nat.succ n) = (nat.toNat n).succ := rfl

noncomputable
def nat.rec (motive: nat -> Sort u)
  (zero: motive 0)
  (succ: ∀n, motive n -> motive n.succ):
  ∀n: nat, motive n
| 0 => zero
| .succ n => succ _ (nat.rec motive zero succ n)

def nat.cases (motive: nat -> Sort u)
  (zero: motive 0)
  (succ: ∀n: nat, motive n.succ):
  ∀n: nat, motive n
| 0 => zero
| .succ _ => succ _

def nat.rec.zero {zero} {succ} : nat.rec motive zero succ 0 = zero := rfl
def nat.rec.succ {zero} {succ} : nat.rec motive zero succ (nat.succ n) = succ n (nat.rec motive zero succ n) := rfl

def nat.noConfusion :
  {P : Sort u_1} → {v1 v2 : Nat} → v1 = v2 → Nat.noConfusionType P v1 v2 := by
  intro P v1 v2 h
  match v1, v2 with
  | 0, 0 => exact id
  | v1 + 1, v2 + 1 =>
    intro ih
    apply ih
    apply Nat.succ.inj h

def nat.succ.inj : Function.Injective nat.succ := fun {_ _} => Nat.succ.inj

def nat.zero_ne_succ (a: nat) : 0 ≠ a.succ := nat.noConfusion
def nat.succ_ne_zero (a: nat) : a.succ ≠ 0 := nat.noConfusion
macro_rules
| `(tactic|contradiction) => `(tactic|exfalso; apply nat.zero_ne_succ; assumption)
macro_rules
| `(tactic|contradiction) => `(tactic|exfalso; apply nat.succ_ne_zero; assumption)

-- seal nat so that you can't see that it's really just Nat
attribute [irreducible] nat
attribute [match_pattern] nat.zero
attribute [match_pattern] nat.succ

def nat.ne_succ_self (a: nat) : a ≠ a.succ := by
  intro h
  induction a using rec with
  | zero => contradiction
  | succ _ ih =>
    apply ih
    apply nat.succ.inj
    assumption
macro_rules
| `(tactic|contradiction) => `(tactic|exfalso; apply nat.ne_succ_self; assumption)
macro_rules
| `(tactic|contradiction) => `(tactic|exfalso; apply nat.ne_succ_self; symm; assumption)

section add

def nat.addFast (a b: nat) : nat := nat.ofNat (nat.toNat a + nat.toNat b)
-- noncomputable for now, until we csimp and redefine Add nat
-- this way lean doesn't try to compile nat.add at all
noncomputable
def nat.add (a b: nat) : nat := a.rec _ b (fun _ => nat.succ)
noncomputable
instance : Add nat := ⟨nat.add⟩

@[simp]
def nat.zero_add (a: nat) : 0 + a = a := rfl
@[simp]
def nat.succ_add (a b: nat) : nat.succ a + b = nat.succ (a + b) := rfl

@[simp]
def nat.add_zero (a: nat) : a + 0 = a := by
  induction a using rec with
  | zero => rfl
  | succ a ih => simp [ih]

@[simp]
def nat.add_succ (a b: nat) : a + b.succ = nat.succ (a + b) := by
  induction a using rec with
  | zero => rfl
  | succ a ih => simp [ih]

def nat.add_comm (a b: nat) : a + b = b + a := by
  induction a using rec with
  | zero => simp
  | succ a ih => simp [ih]

def nat.add_assoc (a b c: nat) : a + b + c = a + (b + c) := by
  induction a using rec with
  | zero => simp
  | succ a ih => simp [ih]

instance : @Std.Commutative nat (· + ·) := ⟨nat.add_comm⟩
instance : @Std.Associative nat (· + ·) := ⟨nat.add_assoc⟩

def nat.lift_add (a b: nat) : a + b = nat.ofNat (a.toNat + b.toNat) := by
  induction a using nat.rec with
  | zero => simp
  | succ a ih =>
    simp [←ih]
    rw [Nat.add_assoc _ 1, Nat.add_comm 1, ←Nat.add_assoc, Nat.add_one,
      nat.ofNat_succ, ih]

def nat.lift_add₁ : nat.ofNat (a + b) = nat.ofNat a + nat.ofNat b := by
  rw [lift_add, toNat.LeftInverse, toNat.LeftInverse]

def nat.lift_add₂ : nat.toNat (a + b) = nat.toNat a + nat.toNat b := by
  conv => { lhs; rw [←nat.ofNat.LeftInverse a, ←nat.ofNat.LeftInverse b] }
  rw [←lift_add₁, nat.toNat.LeftInverse]

@[csimp]
def nat.add_eq_addFast : @nat.add = @nat.addFast := by
  funext a b
  apply lift_add
instance : Add nat := ⟨nat.add⟩

def nat.add_comm_left (a b c: nat) : a + (b + c) = b + (a + c) := by
  simp only [nat.add_comm, ←nat.add_assoc _ a, nat.add_assoc a]
def nat.add_comm_right (a b c: nat) : a + (b + c) = c + (b + a) := by
  simp only [nat.add_comm, ←nat.add_assoc _ a, nat.add_assoc a]
def nat.add_left_comm (a b c: nat) : (a + b) + c = (c + b) + a := by
  simp only [nat.add_comm, ←nat.add_assoc _ a, nat.add_assoc a]
def nat.add_right_comm (a b c: nat) : (a + b) + c = (a + c) + b := by
  simp only [nat.add_comm, ←nat.add_assoc _ a, nat.add_assoc a]

def nat.add_eq_zero {a b: nat} : a + b = 0 -> a = 0 ∧ b = 0 := by
  intro h
  cases a using cases
  cases b using cases
  trivial
  rw [add_succ] at h
  contradiction
  contradiction

end add

section mul

def nat.mulFast (a b: nat) : nat := nat.ofNat (nat.toNat a * nat.toNat b)
-- noncomputable for now, until we csimp and redefine Mul nat
-- this way lean doesn't try to compile nat.mul at all
noncomputable
def nat.mul (a b: nat) : nat := a.rec _ 0 (fun _ => (b + ·))
noncomputable
instance : Mul nat := ⟨nat.mul⟩

@[simp]
def nat.zero_mul (a: nat) : 0 * a = 0 := rfl
@[simp]
def nat.succ_mul (a b: nat) : nat.succ a * b = b + a * b := rfl

@[simp]
def nat.mul_zero (a: nat) : a * 0 = 0 := by
  induction a using rec with
  | zero => rfl
  | succ a ih => simp [ih]

@[simp]
def nat.mul_succ (a b: nat) : a * b.succ = a + a * b := by
  induction a using rec with
  | zero => rfl
  | succ a ih =>
    simp [ih, ←add_succ]
    rw [add_comm_left]

def nat.mul_comm (a b: nat) : a * b = b * a := by
  induction a using rec with
  | zero => simp
  | succ a ih => simp [ih]

@[simp]
def nat.add_mul (a b k: nat) : (a + b) * k = a * k + b * k := by
  induction k using rec with
  | zero => simp
  | succ k ih => simp [ih, add_comm_left, add_assoc]

@[simp]
def nat.mul_add (a b k: nat) : k * (a + b) = k * a + k * b := by
  simp [mul_comm k, add_mul]

def nat.mul_assoc (a b c: nat) : a * b * c = a * (b * c) := by
  induction a using rec with
  | zero => simp
  | succ a ih => simp [ih]

instance : @Std.Commutative nat (· * ·) := ⟨nat.mul_comm⟩
instance : @Std.Associative nat (· * ·) := ⟨nat.mul_assoc⟩

def nat.lift_mul (a b: nat) : a * b = nat.ofNat (a.toNat * b.toNat) := by
  induction a using nat.rec with
  | zero => simp
  | succ a ih =>
    simp [←ih]
    rw [Nat.add_one, Nat.succ_mul, Nat.add_comm, lift_add₁, ofNat.LeftInverse, ih]

def nat.lift_mul₁ : nat.ofNat (a * b) = nat.ofNat a * nat.ofNat b := by
  rw [lift_mul, toNat.LeftInverse, toNat.LeftInverse]

def nat.lift_mul₂ : nat.toNat (a * b) = nat.toNat a * nat.toNat b := by
  conv => { lhs; rw [←nat.ofNat.LeftInverse a, ←nat.ofNat.LeftInverse b] }
  rw [←lift_mul₁, nat.toNat.LeftInverse]

@[csimp]
def nat.mul_eq_mulFast : @nat.mul = @nat.mulFast := by
  funext a b
  apply lift_mul
instance : Mul nat := ⟨nat.mul⟩

def nat.mul_comm_left (a b c: nat) : a * (b * c) = b * (a * c) := by
  simp only [nat.mul_comm, ←nat.mul_assoc _ a, nat.mul_assoc a]
def nat.mul_comm_right (a b c: nat) : a * (b * c) = c * (b * a) := by
  simp only [nat.mul_comm, ←nat.mul_assoc _ a, nat.mul_assoc a]
def nat.mul_left_comm (a b c: nat) : (a * b) * c = (c * b) * a := by
  simp only [nat.mul_comm, ←nat.mul_assoc _ a, nat.mul_assoc a]
def nat.mul_right_comm (a b c: nat) : (a * b) * c = (a * c) * b := by
  simp only [nat.mul_comm, ←nat.mul_assoc _ a, nat.mul_assoc a]

def nat.mul_one (a: nat) : a * 1 = a := by
  show a * nat.succ 0 = a
  rw [nat.mul_succ, nat.mul_zero, nat.add_zero]
def nat.one_mul (a: nat) : 1 * a = a := by
  rw [mul_comm, mul_one]

def nat.of_mul_eq_zero {a b: nat} : a * b = 0 -> a = 0 ∨ b = 0 := by
  intro h
  cases a using cases
  left; rfl
  cases b using cases
  right; rfl
  simp at h
  contradiction

def nat.of_mul_eq_one {a b: nat} : a * b = 1 -> a = 1 ∧ b = 1 := by
  intro h
  cases a using cases with
  | zero =>
    rw [zero_mul] at h
    contradiction
  | succ a =>
  cases a using cases with
  | zero =>
    erw [one_mul] at h
    apply And.intro <;> trivial
  | succ a =>
    rw [succ_mul, succ_mul, ←add_assoc] at h
    cases b using cases
    rw [mul_zero] at h
    contradiction
    rw [add_succ, succ_add, succ_add, succ_add] at h
    replace h : _ = nat.succ 0 := h
    have := nat.succ.inj h
    contradiction

end mul

section pow

def nat.pow (x: nat) (n: Nat) : nat := nat.ofNat (Nat.pow x.toNat n)

instance : Pow nat Nat := ⟨nat.pow⟩

def nat.npow_zero (x: nat) : x ^ 0 = 1 := rfl
def nat.npow_succ (x: nat) (n: Nat) : x ^ (n + 1) = x * x ^ n := by
  show nat.ofNat (_ * _) = _ * nat.ofNat _
  rw [lift_mul₁, ofNat.LeftInverse, mul_comm]

def nat.pow_eq_one {a: nat} : a ^ b = 1 ↔ a = 1 ∨ b = 0 := by
  apply flip Iff.intro
  intro h
  cases h
  subst a
  · induction b with
    | zero => rfl
    | succ b ih =>
      rw [npow_succ, ih]
      rfl
  subst b
  rfl
  intro h
  cases b
  right; rfl
  rw [npow_succ] at h
  have := of_mul_eq_one h
  left; exact this.left

def nat.pow_mul (a: nat) (n m: Nat) : a ^ n * a ^ m = a ^ (n + m) := by
  induction n with
  | zero =>  rw [npow_zero, one_mul, Nat.zero_add]
  | succ n ih => rw [npow_succ, Nat.succ_add, ←Nat.add_one, npow_succ, mul_assoc, ih]

end pow

def nat.iso : nat ≃ Nat where
  toFun := nat.toNat
  invFun := nat.ofNat
  leftInv := by apply nat.ofNat.LeftInverse
  rightInv := by apply nat.toNat.LeftInverse

section sub

def nat.pred : nat -> nat := nat.cases _ 0 id

def nat.succ_pred (a: nat) : a.succ.pred = a := rfl

noncomputable
def nat.sub (a b: nat) : nat := b.rec (fun _ => nat) a (fun _ => nat.pred)
def nat.subFast (a b: nat) : nat := nat.ofNat (a.toNat - b.toNat)

noncomputable
instance : Sub nat := ⟨nat.sub⟩

@[simp]
def nat.sub_zero (n: nat) : n - 0 = n := rfl
@[simp]
def nat.zero_sub (n: nat) : 0 - n = 0 := by
  induction n using rec with
  | zero => rfl
  | succ n ih =>
    show (0 - n).pred = 0
    rw [ih]
    rfl
@[simp]
def nat.succ_sub_succ (a b: nat) : a.succ - b.succ = a - b := by
  show (a.succ - b).pred = a - b
  induction b using rec with
  | zero => rfl
  | succ b ih =>
    show (a.succ - b).pred.pred = a - b.succ
    rw [ih]
    rfl
def nat.add_sub_cancel (a b: nat) : a + b - b = a := by
  induction b using rec with
  | zero => simp
  | succ b ih => simp [ih]

def nat.lift_sub : a - b = nat.ofNat (a.toNat - b.toNat) := by
  induction a using rec generalizing b with
  | zero => simp
  | succ a ih =>
    cases b using nat.cases with
    | zero => simp
    | succ b => simp [ih]

def nat.lift_sub₁ : nat.ofNat (a - b) = nat.ofNat a - nat.ofNat b := by
  rw [lift_sub, toNat.LeftInverse, toNat.LeftInverse]

def nat.lift_sub₂ : nat.toNat (a - b) = nat.toNat a - nat.toNat b := by
  conv => { lhs; rw [←nat.ofNat.LeftInverse a, ←nat.ofNat.LeftInverse b] }
  rw [←lift_sub₁, nat.toNat.LeftInverse]

@[csimp]
def nat.sub_eq_subFast : nat.sub = nat.subFast := by
  funext a b
  apply lift_sub

instance : Sub nat := ⟨nat.sub⟩

@[simp]
def nat.sub_add (a b k: nat) : k - (a + b) = k - a - b := by
  induction a using rec generalizing k with
  | zero => simp
  | succ a ih =>
    cases k using cases with
    | zero => simp
    | succ k => simp [ih]

@[simp]
def nat.sub_mul (a b k: nat) : (a - b) * k = a * k - b * k := by
  induction a using rec generalizing b with
  | zero => simp
  | succ a ih =>
    cases b using cases with
    | zero => simp
    | succ b =>
      simp [ih]
      rw [add_comm k, nat.add_sub_cancel]

@[simp]
def nat.mul_sub (a b k: nat) : k * (a - b) = k * a - k * b := by
  simp [mul_comm k]

end sub
