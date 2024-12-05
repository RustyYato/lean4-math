import Math.Data.Nat.Basic
import Math.Ops.Abs

section
unseal nat

-- use a different namespace so that
def int := Int

instance : Repr int := instReprInt

def int.toInt : int -> Int := id
def int.ofInt : Int -> int := id

@[simp]
def int.ofInt.LeftInverse : ∀x, int.ofInt (int.toInt x) = x := fun _ => rfl
@[simp]
def int.toInt.LeftInverse : ∀x, int.toInt (int.ofInt x) = x := fun _ => rfl

instance : OfNat int n := ⟨.ofNat n⟩

def int.zero : int := 0
def int.ofNat : nat -> int := Int.ofNat
def int.negSucc : nat -> int := Int.negSucc

@[simp]
def int.ofInt_zero : int.ofInt 0 = 0 := rfl
@[simp]
def int.ofInt_one : int.ofInt 1 = 1 := rfl
@[simp]
def int.ofInt_ofNat : int.ofInt (Int.ofNat n) = int.ofNat (nat.ofNat n) := rfl
@[simp]
def int.ofInt_negSucc : int.ofInt (Int.negSucc n) = int.negSucc (nat.ofNat n) := rfl
@[simp]
def int.toInt_zero : int.toInt 0 = 0 := rfl
@[simp]
def int.toInt_one : int.toInt 1 = 1 := rfl
@[simp]
def int.toInt_ofNat : int.toInt (int.ofNat n) = Int.ofNat n.toNat := rfl
@[simp]
def int.toInt_negSucc : int.toInt (int.negSucc n) = int.negSucc n.toNat := rfl

instance decEQ (a b: int) : Decidable (a = b) :=
  have : DecidableEq Int := inferInstance
  this a b

noncomputable
def int.rec (motive: int -> Sort u)
  (ofNat: ∀n, motive (ofNat n))
  (negSucc: ∀n, motive (negSucc n)):
  ∀n: int, motive n
| .ofNat n => ofNat n
| .negSucc n => negSucc n

def int.noConfusion :
  {P : Sort u_1} → {v1 v2 : Int} → v1 = v2 → Int.noConfusionType P v1 v2 := by
  intro P v1 v2 h
  match v1, v2 with
  | .ofNat v1, .ofNat v2 =>
    intro h
    apply h
    apply Int.ofNat.inj
    assumption
  | .negSucc v1, .negSucc v2 =>
    intro h
    apply h
    apply Int.negSucc.inj
    assumption

def int.ofNat.inj : Function.Injective int.ofNat := fun {_ _} => Int.ofNat.inj
def int.negSucc.inj : Function.Injective int.negSucc := fun {_ _} => Int.negSucc.inj

def int.ofNat_ne_negSucc (a b: nat) : ofNat a ≠ negSucc b := int.noConfusion
def int.negSucc_ne_ofNat (a b: nat) : negSucc a ≠ ofNat b := int.noConfusion
macro_rules
| `(tactic|contradiction) => `(tactic|exfalso; apply int.zero_ne_succ; assumption)
macro_rules
| `(tactic|contradiction) => `(tactic|exfalso; apply int.succ_ne_zero; assumption)

-- seal int so that you can't see that it's really just Int
attribute [irreducible] int
attribute [match_pattern] int.zero
attribute [match_pattern] int.ofNat
attribute [match_pattern] int.negSucc

end

namespace int

section neg

def posSucc : nat -> int := (ofNat ·.succ)

noncomputable
def rec' (motive: int -> Sort _)
  (zero: motive 0)
  (posSucc : ∀a: nat, motive (posSucc a))
  (negSucc : ∀a: nat, motive (negSucc a)):
  ∀x, motive x := rec motive (fun x => x.cases (fun n => motive (ofNat n)) zero posSucc) negSucc

noncomputable
def neg : int -> int :=
  rec' (fun _ => int) 0 negSucc posSucc

def negFast (x: int) : int :=
  ofInt (-x.toInt)

@[csimp]
def neg_eq_negFast : neg = negFast := by
  funext x
  cases x using rec' <;> rfl

instance : Neg int := ⟨neg⟩

@[simp]
def neg_zero : -(0: int) = 0 := rfl
def neg_ofNat_succ : -ofNat n.succ = negSucc n := rfl
@[simp]
def neg_negSucc : -negSucc n = posSucc n := rfl
@[simp]
def neg_posSucc : -posSucc n = negSucc n := rfl

@[simp]
def neg_neg (x: int) : - -x = x := by
  cases x using rec' <;> rfl

def neg.inj : Function.Injective neg := Function.IsLeftInverse.Injective neg_neg

end neg

section succ_pred

noncomputable
def succ : int -> int :=
  rec _ (fun n => ofNat n.succ) (fun n => n.cases (fun _ => int) 0 (fun n => negSucc n))

def fastSucc (a: int) : int := ofInt (a.toInt + 1)

noncomputable
def pred : int -> int :=
  rec _ (fun n => n.cases (fun _ => int) (negSucc 0) (fun n => ofNat n)) (fun n => negSucc n.succ)

def fastPred (a: int) : int := ofInt (a.toInt - 1)

@[simp]
def ofInt_succ : (ofInt a).succ = ofInt (a + 1) := by
  cases a
  rfl
  rename_i a
  cases a <;> rfl
@[simp]
def ofInt_pred : (ofInt a).pred = ofInt (a - 1) := by
  cases a
  rename_i a
  cases a
  rfl
  rename_i a
  show _ = ofInt (Int.ofNat a + 1 - 1)
  rw [Int.add_sub_cancel]
  rfl
  rfl
@[simp]
def toInt_succ : toInt a.succ = (toInt a) + 1 := by
  conv => { lhs; rw [←ofInt.LeftInverse a, ofInt_succ] }
  rw [toInt.LeftInverse]
@[simp]
def toInt_pred : toInt a.pred = (toInt a) - 1 := by
  conv => { lhs; rw [←ofInt.LeftInverse a, ofInt_pred] }
  rw [toInt.LeftInverse]

@[csimp]
def succ_eq_fastSucc : succ = fastSucc := by
  funext a
  unfold fastSucc
  rw [←ofInt_succ]
  rfl
@[csimp]
def pred_eq_fastPred : pred = fastPred := by
  funext a
  unfold fastPred
  rw [←ofInt_pred]
  rfl

@[simp]
def succ_pred (a: int) : a.succ.pred = a := by
  cases a using rec
  rfl
  rename_i a
  cases a using nat.cases <;> rfl

@[simp]
def pred_succ (a: int) : a.pred.succ = a := by
  cases a using rec
  rename_i a
  cases a using nat.cases <;> rfl
  rfl

def succ.inj : Function.Injective succ := Function.IsLeftInverse.Injective succ_pred
def pred.inj : Function.Injective pred := Function.IsLeftInverse.Injective pred_succ

@[simp]
def succ_ofNat : (ofNat a).succ = ofNat a.succ := rfl
@[simp]
def pred_negSucc : (negSucc a).pred = negSucc a.succ := rfl
@[simp]
def pred_ofNat_succ : (ofNat a.succ).pred = ofNat a := rfl
@[simp]
def succ_negSucc_succ : (negSucc a.succ).succ = negSucc a := rfl
@[simp]
def pred_zero : pred 0 = negSucc 0 := rfl

@[simp]
def succ_posSucc : (posSucc a).succ = posSucc a.succ := rfl
@[simp]
def pred_posSucc : (posSucc a).pred = ofNat a := rfl

@[simp]
def neg_pred (a: int) : -a.pred = (-a).succ := by
  cases a using rec' <;> rfl
@[simp]
def neg_succ (a: int) : -a.succ = (-a).pred := by
  cases a using rec'
  any_goals rfl
  rename_i a; cases a using nat.rec <;> rfl
@[simp]
def neg_ofNat (a: nat) : -ofNat a = (negSucc a).succ := by
  erw [←succ_pred (ofNat a), neg_pred, neg_ofNat_succ]
noncomputable
def ind (motive: int -> Sort _)
  (zero: motive 0)
  (succ: ∀a, motive a -> motive a.succ)
  (pred: ∀a, motive a -> motive a.pred) : ∀x, motive x := by
  intro x
  cases x using rec with
  | ofNat x =>
    induction x using nat.rec with
    | zero => exact zero
    | succ x =>
      apply succ (.ofNat x)
      assumption
  | negSucc x =>
    induction x using nat.rec with
    | zero =>
      apply pred 0
      exact zero
    | succ x =>
      apply pred (.negSucc x)
      assumption

structure ind_sound (motive: int -> Sort _)
  (zero: motive 0)
  (succ: ∀a, motive a -> motive a.succ)
  (pred: ∀a, motive a -> motive a.pred) : Prop where
  zero_eq_succ: zero = succ _ (ind motive zero succ pred (negSucc 0))
  succ_pred: ∀a, HEq (ind motive zero succ pred a) (pred _ (succ _ <| ind motive zero succ pred a))
  pred_succ: ∀a, HEq (ind motive zero succ pred a) (succ _ (pred _ <| ind motive zero succ pred a))

variable
  {motive: int -> Sort _}
  {zero: motive 0}
  {succ: ∀a, motive a -> motive a.succ}
  {pred: ∀a, motive a -> motive a.pred}
  (sound: ind_sound motive zero succ pred)
  {a: int}

def ind_zero : ind motive zero succ pred 0 = zero := rfl
def ind_hcongr (h: a = b) : HEq (ind motive zero succ pred a) (ind motive zero succ pred b) := by
  rw [h]
def ind_spec :
  ind motive zero succ pred a.succ =
  succ _ (ind motive zero succ pred a) ∧
  ind motive zero succ pred a.pred =
  pred _ (ind motive zero succ pred a)
  := by
  cases  a using rec with
  | ofNat a =>
    cases a using nat.cases with
    | zero => trivial
    | succ n =>
      apply And.intro rfl
      show ind _ _ _ _ (ofNat n) = _
      show ind motive zero succ pred (ofNat n) = pred (ofNat n.succ)
        (succ _ (ind motive zero succ pred (ofNat n)))
      apply eq_of_heq
      apply flip HEq.trans
      apply sound.succ_pred (ofNat n)
      rfl
  | negSucc a =>
    induction a using nat.rec with
    | zero => exact And.intro sound.zero_eq_succ rfl
    | succ n ih =>
      apply And.intro _ rfl
      show _ = succ (negSucc n.succ)
        (pred _ (ind motive zero succ pred (negSucc n)))
      apply eq_of_heq
      apply flip HEq.trans
      apply sound.pred_succ (negSucc n)
      rfl
def ind_succ :
  ind motive zero succ pred a.succ =
  succ _ (ind motive zero succ pred a)
  := (ind_spec sound).left
def ind_pred :
  ind motive zero succ pred a.pred =
  pred _ (ind motive zero succ pred a)
  := (ind_spec sound).right

end succ_pred

section add

noncomputable
def add (a b: int) : int :=
  a.ind (fun _ => int) b (fun _ ih => ih.succ) (fun _ ih => ih.pred)
def addFast (a b: int) : int :=
  ofInt (a.toInt + b.toInt)

noncomputable
instance : Add int := ⟨.add⟩

def add_sound : ind_sound (fun _ => int) b (fun _ ih => ih.succ) (fun _ ih => ih.pred) where
  zero_eq_succ := (pred_succ _).symm
  succ_pred := by simp
  pred_succ := by simp

@[simp]
def zero_add (a: int) : 0 + a = a := rfl
@[simp]
def succ_add (a b: int) : a.succ + b = (a + b).succ := by
  show add _ _ = _
  apply ind_succ
  apply add_sound
@[simp]
def pred_add (a b: int) : a.pred + b = (a + b).pred := by
  show add _ _ = pred (add _ _)
  apply ind_pred
  apply add_sound

@[csimp]
def add_eq_addFast : add = addFast := by
  funext a b
  show a + b = _
  unfold addFast
  induction a using ind with
  | zero =>
    erw [zero_add, Int.zero_add]
    rfl
  | succ a ih =>
    rw [toInt_succ, Int.add_comm _ 1, Int.add_assoc, Int.add_comm 1]
    simp [ih]
  | pred a ih =>
    rw [toInt_pred, Int.sub_eq_add_neg, Int.add_comm _ (-1), Int.add_assoc, Int.add_comm (-1), ←Int.sub_eq_add_neg]
    simp [ih]

instance : Add int := ⟨.add⟩

@[simp]
def add_zero (a: int) : a + 0 = a := by
  induction a using ind with
  | zero => rfl
  | succ a ih => simp [ih]
  | pred a ih => simp [ih]
@[simp]
def add_succ (a b: int) : a + b.succ = (a + b).succ := by
  induction a using ind with
  | zero => rfl
  | succ a ih => simp [ih]
  | pred a ih => simp [ih]
@[simp]
def add_pred (a b: int) : a + b.pred = (a + b).pred := by
  induction a using ind with
  | zero => rfl
  | succ a ih => simp [ih]
  | pred a ih => simp [ih]

def add_comm (a b: int) : a + b = b + a := by
  induction a using ind with
  | zero => simp
  | succ a ih => simp [ih]
  | pred a ih => simp [ih]

def add_assoc (a b c: int) : a + b + c = a + (b + c) := by
  induction a using ind with
  | zero => simp
  | succ a ih => simp [ih]
  | pred a ih => simp [ih]

instance : @Std.Commutative int (· + ·) := ⟨add_comm⟩
instance : @Std.Associative int (· + ·) := ⟨add_assoc⟩

@[simp]
def neg_add (a b: int) : -(a + b) = -a + -b := by
  induction a using ind with
  | zero => simp
  | succ a ih => simp [ih]
  | pred a ih => simp [ih]

@[simp]
def add_neg_self (a: int) : a + -a = 0 := by
  induction a using ind with
  | zero => simp
  | succ a ih => simp [ih]
  | pred a ih => simp [ih]; rfl

@[simp]
def neg_self_add (a: int) : -a + a = 0 := by
  rw [add_comm, add_neg_self]

def sub (a b: int) := a + -b
def subFast (a b: int) := ofInt (a.toInt - b.toInt)

@[csimp]
def sub_eq_subFast : sub = subFast := by
  funext a b
  unfold sub subFast
  show add _ (neg _) = _
  rw [add_eq_addFast, neg_eq_negFast]
  rfl

instance : Sub int := ⟨sub⟩

def sub_eq_add_neg (a b: int) : a - b = a + -b := rfl
@[simp]
def sub_self (a: int) : a - a = 0 := add_neg_self a

def sub_assoc (a b c: int) : a - b - c = a - (b + c) := by
  simp [sub_eq_add_neg, add_assoc]
def sub_add_assoc (a b c: int) : a - b + c = a - (b - c) := by
  simp [sub_eq_add_neg, add_assoc]
def add_sub_assoc (a b c: int) : a + b - c = a + (b - c) := by
  simp [sub_eq_add_neg, add_assoc]

@[simp]
def sub_add_cancel (a b: int) : a - b + b = a := by
  simp [sub_eq_add_neg, add_assoc]

@[simp]
def add_sub_cancel (a b: int) : a + b - b = a := by
  simp [sub_eq_add_neg, add_assoc]

@[simp]
def zero_sub (a: int) : 0 - a = -a := rfl

@[simp]
def sub_zero (a: int) : a - 0 = a := add_zero _

@[simp]
def add_one (a: int) : a + 1 = a.succ := by
  induction a using ind with
  | zero => rfl
  | succ a ih => simp [ih]
  | pred a ih => simp [ih]
@[simp]
def add_neg_one (a: int) : a + -1 = a.pred := by
  induction a using ind with
  | zero => rfl
  | succ a ih => simp [ih]
  | pred a ih => simp [ih]
@[simp]
def sub_one (a: int) : a - 1 = a.pred := add_neg_one _
@[simp]
def sub_neg_one (a: int) : a - -1 = a.succ := add_one _

@[simp]
def sub_pred (a b: int) : a - b.pred = (a - b).succ := by simp [sub_eq_add_neg]
@[simp]
def sub_succ (a b: int) : a - b.succ = (a - b).pred := by simp [sub_eq_add_neg]
@[simp]
def succ_sub (a b: int) : a.succ - b = (a - b).succ := by simp [sub_eq_add_neg]
@[simp]
def pred_sub (a b: int) : a.pred - b = (a - b).pred := by simp [sub_eq_add_neg]

@[simp]
def neg_sub (a b: int) : -(a - b) = b - a := by
  induction a using ind with
  | zero => simp
  | succ a ih => simp [ih]
  | pred a ih => simp [ih]

@[simp]
def ofNat_succ (a: nat ) : (ofNat a).succ = ofNat a.succ := by
  rfl

@[simp]
def ofNat_add (a b: nat ) : ofNat a + ofNat b = ofNat (a + b) := by
  induction a using nat.rec generalizing b with
  | zero => rfl
  | succ a ih =>
    rw [←ofNat_succ a, succ_add]
    simp [ih]

@[simp]
def posSucc_add (a b: nat ) : posSucc a + posSucc b = posSucc (a + b).succ := by
  apply neg.inj
  show -_ = (-_: int)
  simp [posSucc]

@[simp]
def negSucc_add (a b: nat ) : negSucc a + negSucc b = negSucc (a + b).succ := by
  apply neg.inj
  show -_ = (-_: int)
  simp

def add_comm_left (a b c: int) : a + (b + c) = b + (a + c) := by
  simp only [add_comm, ←add_assoc _ a, add_assoc a]
def add_comm_right (a b c: int) : a + (b + c) = c + (b + a) := by
  simp only [add_comm, ←add_assoc _ a, add_assoc a]
def add_left_comm (a b c: int) : (a + b) + c = (c + b) + a := by
  simp only [add_comm, ←add_assoc _ a, add_assoc a]
def add_right_comm (a b c: int) : (a + b) + c = (a + c) + b := by
  simp only [add_comm, ←add_assoc _ a, add_assoc a]

@[simp]
def add_left_iff {a b k: int} : k + a = k + b ↔ a = b := by
  symm; apply Iff.intro
  intro h; subst h; rfl
  intro h
  induction k using ind with
  | zero => assumption
  | succ k ih =>
    apply ih
    rw [succ_add, succ_add] at h
    apply succ.inj
    assumption
  | pred k ih =>
    apply ih
    rw [pred_add, pred_add] at h
    apply pred.inj
    assumption
@[simp]
def add_right_iff {a b k: int} : a + k = b + k ↔ a = b := by
  simp [add_comm _ k]

@[simp]
def sub_eq_zero_iff {a b: int} : a - b = 0 ↔ a = b := by
  apply Iff.intro
  intro h
  have : a - b + b = 0 + b := add_right_iff.mpr h
  simp at this
  assumption
  intro h
  simp [h]

@[simp]
def sub_neg {a b: int} : a - -b = a + b := by rw [sub_eq_add_neg, neg_neg]

end add

section mul

noncomputable
def mul (a b: int) : int :=
  a.ind (fun _ => int) 0 (fun _ ih =>  ih + b) (fun _ ih =>  ih - b)
def mulFast (a b: int) : int := ofInt (a.toInt * b.toInt)

noncomputable
instance : Mul int := ⟨.mul⟩

def mul_sound : ind_sound (fun _ => int) 0 (fun _ ih =>  ih + b) (fun _ ih =>  ih - b) where
  zero_eq_succ := (sub_add_cancel _ _).symm
  succ_pred a := by simp
  pred_succ a := by simp

@[simp]
def zero_mul (a: int) : 0 * a = 0 := rfl
@[simp]
def neg_one_mul (a: int) : -1 * a = -a := rfl
@[simp]
def succ_mul (a b: int) : a.succ * b = a * b + b := by
  show mul _ _ = _
  apply ind_succ
  apply mul_sound
@[simp]
def pred_mul (a b: int) : a.pred * b = a * b - b := by
  show mul _ _ = _
  apply ind_pred
  apply mul_sound

@[csimp]
def mul_eq_mulFast : mul = mulFast := by
  funext a b
  show a * b = a.mulFast b
  unfold mulFast
  induction a using ind with
  | zero =>
    erw [Int.zero_mul]
    rfl
  | succ a ih =>
    rw [succ_mul, toInt_succ, Int.add_mul, Int.one_mul]
    show add _ _ = _
    rw [add_eq_addFast, ih]
    rfl
  | pred a ih =>
    rw [pred_mul, toInt_pred, Int.sub_mul, Int.one_mul]
    show sub _ _ = _
    rw [sub_eq_subFast, ih]
    rfl

instance : Mul int := ⟨.mul⟩

@[simp]
def mul_zero (a: int) : a * 0 = 0 := by
  induction a using ind with
  | zero => rfl
  | succ a ih => simp [ih]
  | pred a ih => simp [ih]

@[simp]
def mul_neg_one (a: int) : a * -1 = -a := by
  induction a using ind with
  | zero => rfl
  | succ a ih => simp [ih]
  | pred a ih => simp [ih]

@[simp]
def mul_succ (a b: int) : a * b.succ = a * b + a := by
  induction a using ind with
  | zero => rfl
  | succ a ih => simp [ih, add_assoc, add_comm a]
  | pred a ih => simp [ih, sub_eq_add_neg, add_assoc, add_comm a]

@[simp]
def mul_pred (a b: int) : a * b.pred = a * b - a := by
  induction a using ind with
  | zero => rfl
  | succ a ih => simp [ih, sub_eq_add_neg, add_assoc, add_comm b]
  | pred a ih => simp [ih, sub_eq_add_neg, add_assoc, add_comm (-a)]

def mul_comm (a b: int) : a * b = b * a := by
  induction a using ind with
  | zero => simp
  | succ a ih => simp [ih]
  | pred a ih => simp [ih]

def mul_neg (a b: int) : a * -b = -(a * b) := by
  induction a using ind with
  | zero => simp
  | succ a ih => simp [ih]
  | pred a ih => simp [ih, sub_eq_add_neg]

def neg_mul (a b: int) : -a * b = -(a * b) := by
  simp [mul_comm _ b, mul_neg]

@[simp]
def add_mul (a b k: int) : (a + b) * k = a * k + b * k := by
  induction k using ind with
  | zero => simp
  | succ k ih => simp [ih]; ac_rfl
  | pred k ih => simp [ih, sub_eq_add_neg]; ac_rfl

@[simp]
def mul_add (a b k: int) : k * (a + b) = k * a + k * b := by
  simp [mul_comm k]

@[simp]
def mul_sub (a b k: int) : k * (a - b) = k * a - k * b := by
  simp [mul_comm k, sub_eq_add_neg, neg_mul]

@[simp]
def sub_mul (a b k: int) : (a - b) * k = a * k - b * k := by
  simp [mul_comm _ k]

def mul_assoc (a b c: int) : a * b * c = a * (b * c) := by
  induction a using ind with
  | zero => simp
  | succ a ih => simp [ih]
  | pred a ih => simp [ih]

instance : @Std.Commutative int (· * ·) := ⟨mul_comm⟩
instance : @Std.Associative int (· * ·) := ⟨mul_assoc⟩

def mul_comm_left (a b c: int) : a * (b * c) = b * (a * c) := by
  simp only [mul_comm, ←mul_assoc _ a, mul_assoc a]
def mul_comm_right (a b c: int) : a * (b * c) = c * (b * a) := by
  simp only [mul_comm, ←mul_assoc _ a, mul_assoc a]
def mul_left_comm (a b c: int) : (a * b) * c = (c * b) * a := by
  simp only [mul_comm, ←mul_assoc _ a, mul_assoc a]
def mul_right_comm (a b c: int) : (a * b) * c = (a * c) * b := by
  simp only [mul_comm, ←mul_assoc _ a, mul_assoc a]

@[simp]
def mul_one (a: int) : a * 1 = a := by
  show a * succ 0 = a
  simp
@[simp]
def one_mul (a: int) : 1 * a = a := by
  show succ 0 * a = a
  simp

def ofNat_mul : ofNat a * ofNat b = ofNat (a * b) := by
  induction a using nat.rec
  erw [zero_mul]; rfl
  rename_i ih
  rw [←ofNat_succ, succ_mul, ih]
  simp [nat.add_comm]

@[simp]
def posSucc_mul : posSucc a * posSucc b = posSucc (a * b + a + b) := by
  simp [posSucc, ofNat_mul]
  ac_rfl

@[simp]
def negSucc_mul : negSucc a * negSucc b = posSucc (a * b + a + b) := by
  rw [←neg_neg (_ * _), ←neg_mul, ←mul_neg, neg_negSucc, neg_negSucc]
  simp

@[simp]
def negSucc_mul_posSucc : negSucc a * posSucc b = negSucc (a * b + a + b) := by
  rw [←neg_posSucc, neg_mul]
  simp [posSucc, ofNat_mul]
  ac_rfl

@[simp]
def posSucc_mul_negSucc : posSucc a * negSucc b = negSucc (a * b + a + b) := by
  rw [←neg_posSucc, mul_neg]
  simp [posSucc, ofNat_mul]
  ac_rfl

def mul_eq_zero {a b: int} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  cases a using rec'
  simp
  all_goals cases b using rec'
  all_goals
    simp
    try exact Iff.intro nofun nofun

def mul_left_cancel_iff {a b k: int} (h: k ≠ 0) : k * a = k * b ↔ a = b := by
  apply flip Iff.intro
  intro h
  rw [h]
  intro h
  induction a using ind generalizing b with
  | zero =>
    rw [mul_zero] at h
    cases mul_eq_zero.mp h.symm
    contradiction
    subst b
    rfl
  | succ a ih =>
    rw [←pred_succ b, mul_succ, mul_succ] at h
    rw [←pred_succ b]
    congr
    apply ih
    suffices k * a + k - k = k * b.pred + k - k by
      rw [add_sub_cancel, add_sub_cancel] at this
      assumption
    rw [h]
  | pred a ih =>
    rw [←succ_pred b, mul_pred, mul_pred] at h
    rw [←succ_pred b]
    congr
    apply ih
    suffices k * a - k + k = k * b.succ - k + k by
      rw [sub_add_cancel, sub_add_cancel] at this
      assumption
    rw [h]
def mul_right_cancel_iff {a b k: int} (h: k ≠ 0) : a * k = b * k ↔ a = b := by
  rw [mul_comm _ k, mul_comm _ k]
  apply mul_left_cancel_iff
  assumption

end mul

section abs

noncomputable
def abs := rec (fun _ => nat) (fun x => x) (fun x => x.succ)

def absFast (a: int) := nat.ofNat a.toInt.natAbs

@[csimp]
def abs_eq_absFast : abs = absFast := by
  funext a
  cases a using rec <;> rfl

instance : AbsoluteValue int nat := ⟨abs⟩

def abs_ofNat : ‖ofNat a‖ = a := rfl
def abs_negSucc : ‖negSucc a‖ = a.succ := rfl
def abs_posSucc : ‖posSucc a‖ = a.succ := rfl
def abs_neg (a: int) : ‖-a‖ = ‖a‖ := by
  cases a using rec' <;> rfl

end abs

end int
