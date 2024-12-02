import Math.Function.Basic

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

@[match_pattern]
def nat.zero : nat := 0
@[match_pattern]
def nat.succ : nat -> nat := Nat.succ

@[simp]
def nat.ofNat_zero : nat.ofNat 0 = 0 := rfl
@[simp]
def nat.ofNat_succ : nat.ofNat (Nat.succ n) = (nat.ofNat n).succ := rfl
@[simp]
def nat.toNat_zero : nat.toNat 0 = 0 := rfl
@[simp]
def nat.toNat_succ : nat.toNat (nat.succ n) = (nat.toNat n).succ := rfl

def nat.rec (motive: nat -> Sort u)
  (zero: motive 0)
  (succ: ∀n, motive n -> motive n.succ):
  ∀n: nat, motive n
| 0 => zero
| .succ n => succ _ (nat.rec motive zero succ n)

def nat.rec.zero {zero} {succ} : nat.rec motive zero succ 0 = zero := rfl
def nat.rec.succ {zero} {succ} : nat.rec motive zero succ (nat.succ n) = succ n (nat.rec motive zero succ n) := rfl

-- seal nat so that you can't see that it's really just Nat
attribute [irreducible] nat

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

def nat.lift_add (a b: nat) : a + b = nat.ofNat (a.toNat + b.toNat) := by
  induction a using nat.rec with
  | zero => simp
  | succ a ih =>
    simp [←ih]
    rw [Nat.add_assoc _ 1, Nat.add_comm 1, ←Nat.add_assoc, Nat.add_one,
      nat.ofNat_succ, ih]

def nat.lift_add' (a b: Nat) : nat.ofNat (a + b) = nat.ofNat a + nat.ofNat b := by
  rw [lift_add, toNat.LeftInverse, toNat.LeftInverse]

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

def nat.lift_mul (a b: nat) : a * b = nat.ofNat (a.toNat * b.toNat) := by
  induction a using nat.rec with
  | zero => simp
  | succ a ih =>
    simp [←ih]
    rw [Nat.add_one, Nat.succ_mul, Nat.add_comm, lift_add', ofNat.LeftInverse, ih]

def nat.lift_mul' (a b: Nat) : nat.ofNat (a * b) = nat.ofNat a * nat.ofNat b := by
  rw [lift_mul, toNat.LeftInverse, toNat.LeftInverse]

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

end mul
