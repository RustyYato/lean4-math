import Math.Data.Nat.Basic

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

section neg

def int.posSucc : nat -> int := (int.ofNat ·.succ)

noncomputable
def int.rec' (motive: int -> Sort _)
  (zero: motive 0)
  (posSucc : ∀a: nat, motive (int.posSucc a))
  (negSucc : ∀a: nat, motive (int.negSucc a)):
  ∀x, motive x := int.rec motive (fun x => x.cases (fun n => motive (int.ofNat n)) zero posSucc) negSucc

noncomputable
def int.neg : int -> int :=
  int.rec' (fun _ => int) 0 int.negSucc int.posSucc

def int.negFast (x: int) : int :=
  int.ofInt (-x.toInt)

@[csimp]
def int.neg_eq_negFast : int.neg = int.negFast := by
  funext x
  cases x using rec' <;> rfl

instance : Neg int := ⟨int.neg⟩

@[simp]
def int.neg_zero : -(0: int) = 0 := rfl
def int.neg_ofNat_succ : -int.ofNat n.succ = int.negSucc n := rfl
def int.neg_negSucc : -int.negSucc n = int.ofNat n.succ := rfl

@[simp]
def int.neg_neg (x: int) : - -x = x := by
  cases x using rec' <;> rfl

noncomputable
def int.rec'' (motive: int -> Sort _)
  (zero: motive 0)
  (neg_one: motive (-1))
  (posSucc : ∀a: nat, motive (int.ofNat a.succ))
  (negSucc : ∀a: nat, motive (int.negSucc a.succ)):
  ∀x, motive x := int.rec motive (fun x => x.cases (fun n => motive (int.ofNat n)) zero posSucc) (fun x => x.cases (fun n => motive (int.negSucc n)) neg_one negSucc)

end neg

section succ_pred

noncomputable
def int.succ : int -> int :=
  int.rec _ (fun n => int.ofNat n.succ) (fun n => n.cases (fun _ => int) 0 (fun n => int.negSucc n))

def int.fastSucc (a: int) : int := int.ofInt (a.toInt + 1)

noncomputable
def int.pred : int -> int :=
  int.rec _ (fun n => n.cases (fun _ => int) (int.negSucc 0) (fun n => int.ofNat n)) (fun n => int.negSucc n.succ)

def int.fastPred (a: int) : int := int.ofInt (a.toInt - 1)

@[simp]
def int.ofInt_succ : (ofInt a).succ = ofInt (a + 1) := by
  cases a
  rfl
  rename_i a
  cases a <;> rfl
@[simp]
def int.ofInt_pred : (ofInt a).pred = ofInt (a - 1) := by
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
def int.toInt_succ : toInt a.succ = (toInt a) + 1 := by
  conv => { lhs; rw [←ofInt.LeftInverse a, ofInt_succ] }
  rw [toInt.LeftInverse]
@[simp]
def int.toInt_pred : toInt a.pred = (toInt a) - 1 := by
  conv => { lhs; rw [←ofInt.LeftInverse a, ofInt_pred] }
  rw [toInt.LeftInverse]

@[csimp]
def int.succ_eq_fastSucc : int.succ = int.fastSucc := by
  funext a
  unfold fastSucc
  rw [←ofInt_succ]
  rfl
@[csimp]
def int.pred_eq_fastPred : int.pred = int.fastPred := by
  funext a
  unfold fastPred
  rw [←ofInt_pred]
  rfl

@[simp]
def int.succ_pred (a: int) : a.succ.pred = a := by
  cases a using rec
  rfl
  rename_i a
  cases a using nat.cases <;> rfl

@[simp]
def int.pred_succ (a: int) : a.pred.succ = a := by
  cases a using rec
  rename_i a
  cases a using nat.cases <;> rfl
  rfl

@[simp]
def int.succ_ofNat : (int.ofNat a).succ = int.ofNat a.succ := rfl
@[simp]
def int.pred_negSucc : (int.negSucc a).pred = int.negSucc a.succ := rfl
@[simp]
def int.pred_ofNat_succ : (int.ofNat a.succ).pred = int.ofNat a := rfl
@[simp]
def int.succ_negSucc_succ : (int.negSucc a.succ).succ = int.negSucc a := rfl
@[simp]
def int.pred_zero : int.pred 0 = int.negSucc 0 := rfl

@[simp]
def int.succ_posSucc : (int.posSucc a).succ = int.posSucc a.succ := rfl
@[simp]
def int.pred_posSucc : (int.posSucc a).pred = int.ofNat a := rfl

@[simp]
def int.neg_pred (a: int) : -a.pred = (-a).succ := by
  cases a using rec' <;> rfl
@[simp]
def int.neg_succ (a: int) : -a.succ = (-a).pred := by
  cases a using rec'
  any_goals rfl
  rename_i a; cases a using nat.rec <;> rfl

noncomputable
def int.ind (motive: int -> Sort _)
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

structure int.ind_sound (motive: int -> Sort _)
  (zero: motive 0)
  (succ: ∀a, motive a -> motive a.succ)
  (pred: ∀a, motive a -> motive a.pred) : Prop where
  zero_eq_succ: zero = succ _ (ind motive zero succ pred (int.negSucc 0))
  succ_pred: ∀a, HEq (ind motive zero succ pred a) (pred _ (succ _ <| ind motive zero succ pred a))
  pred_succ: ∀a, HEq (ind motive zero succ pred a) (succ _ (pred _ <| ind motive zero succ pred a))

variable
  {motive: int -> Sort _}
  {zero: motive 0}
  {succ: ∀a, motive a -> motive a.succ}
  {pred: ∀a, motive a -> motive a.pred}
  (sound: int.ind_sound motive zero succ pred)
  {a: int}

def int.ind_zero : ind motive zero succ pred 0 = zero := rfl
def int.ind_hcongr (h: a = b) : HEq (ind motive zero succ pred a) (ind motive zero succ pred b) := by
  rw [h]
def int.ind_spec :
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
def int.ind_succ :
  ind motive zero succ pred a.succ =
  succ _ (ind motive zero succ pred a)
  := (int.ind_spec sound).left
def int.ind_pred :
  ind motive zero succ pred a.pred =
  pred _ (ind motive zero succ pred a)
  := (int.ind_spec sound).right

end succ_pred

section add

noncomputable
def int.add (a b: int) : int :=
  a.ind (fun _ => int) b (fun _ ih => ih.succ) (fun _ ih => ih.pred)
def int.addFast (a b: int) : int :=
  int.ofInt (a.toInt + b.toInt)

noncomputable
instance : Add int := ⟨.add⟩

def int.add_sound : int.ind_sound (fun _ => int) b (fun _ ih => ih.succ) (fun _ ih => ih.pred) where
  zero_eq_succ := (pred_succ _).symm
  succ_pred := by simp
  pred_succ := by simp

@[simp]
def int.zero_add (a: int) : 0 + a = a := rfl
@[simp]
def int.succ_add (a b: int) : a.succ + b = (a + b).succ := by
  show add _ _ = _
  apply int.ind_succ
  apply int.add_sound
@[simp]
def int.pred_add (a b: int) : a.pred + b = (a + b).pred := by
  show add _ _ = pred (add _ _)
  apply int.ind_pred
  apply int.add_sound

@[csimp]
def int.add_eq_addFast : int.add = int.addFast := by
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
def int.add_zero (a: int) : a + 0 = a := by
  induction a using ind with
  | zero => rfl
  | succ a ih => simp [ih]
  | pred a ih => simp [ih]
@[simp]
def int.add_succ (a b: int) : a + b.succ = (a + b).succ := by
  induction a using ind with
  | zero => rfl
  | succ a ih => simp [ih]
  | pred a ih => simp [ih]
@[simp]
def int.add_pred (a b: int) : a + b.pred = (a + b).pred := by
  induction a using ind with
  | zero => rfl
  | succ a ih => simp [ih]
  | pred a ih => simp [ih]

def int.add_comm (a b: int) : a + b = b + a := by
  induction a using ind with
  | zero => simp
  | succ a ih => simp [ih]
  | pred a ih => simp [ih]

def int.add_assoc (a b c: int) : a + b + c = a + (b + c) := by
  induction a using ind with
  | zero => simp
  | succ a ih => simp [ih]
  | pred a ih => simp [ih]

instance : @Std.Commutative int (· + ·) := ⟨int.add_comm⟩
instance : @Std.Associative int (· + ·) := ⟨int.add_assoc⟩

@[simp]
def int.neg_add (a b: int) : -(a + b) = -a + -b := by
  induction a using ind with
  | zero => simp
  | succ a ih => simp [ih]
  | pred a ih => simp [ih]

@[simp]
def int.add_neg_self (a: int) : a + -a = 0 := by
  induction a using ind with
  | zero => simp
  | succ a ih => simp [ih]
  | pred a ih => simp [ih]; rfl

@[simp]
def int.neg_self_add (a: int) : -a + a = 0 := by
  rw [add_comm, add_neg_self]

def int.sub (a b: int) := a + -b
def int.subFast (a b: int) := ofInt (a.toInt - b.toInt)

@[csimp]
def int.sub_eq_subFast : int.sub = int.subFast := by
  funext a b
  unfold sub subFast
  show add _ (neg _) = _
  rw [add_eq_addFast, neg_eq_negFast]
  rfl

instance : Sub int := ⟨int.sub⟩

def int.sub_eq_add_neg (a b: int) : a - b = a + -b := rfl
@[simp]
def int.sub_self (a: int) : a - a = 0 := add_neg_self a

def int.sub_assoc (a b c: int) : a - b - c = a - (b + c) := by
  simp [sub_eq_add_neg, add_assoc]
def int.sub_add_assoc (a b c: int) : a - b + c = a - (b - c) := by
  simp [sub_eq_add_neg, add_assoc]
def int.add_sub_assoc (a b c: int) : a + b - c = a + (b - c) := by
  simp [sub_eq_add_neg, add_assoc]

def int.sub_add_cancel (a b: int) : a - b + b = a := by
  simp [sub_eq_add_neg, add_assoc]

def int.add_sub_cancel (a b: int) : a + b - b = a := by
  simp [sub_eq_add_neg, add_assoc]

@[simp]
def int.zero_sub (a: int) : 0 - a = -a := rfl

@[simp]
def int.sub_zero (a: int) : a - 0 = a := add_zero _

@[simp]
def int.add_one (a: int) : a + 1 = a.succ := by
  induction a using ind with
  | zero => rfl
  | succ a ih => simp [ih]
  | pred a ih => simp [ih]
@[simp]
def int.add_neg_one (a: int) : a + -1 = a.pred := by
  induction a using ind with
  | zero => rfl
  | succ a ih => simp [ih]
  | pred a ih => simp [ih]
@[simp]
def int.sub_one (a: int) : a - 1 = a.pred := add_neg_one _
@[simp]
def int.sub_neg_one (a: int) : a - -1 = a.succ := add_one _

@[simp]
def int.sub_pred (a b: int) : a - b.pred = (a - b).succ := by simp [sub_eq_add_neg]
@[simp]
def int.sub_succ (a b: int) : a - b.succ = (a - b).pred := by simp [sub_eq_add_neg]
@[simp]
def int.succ_sub (a b: int) : a.succ - b = (a - b).succ := by simp [sub_eq_add_neg]
@[simp]
def int.pred_sub (a b: int) : a.pred - b = (a - b).pred := by simp [sub_eq_add_neg]

@[simp]
def int.neg_sub (a b: int) : -(a - b) = b - a := by
  induction a using ind with
  | zero => simp
  | succ a ih => simp [ih]
  | pred a ih => simp [ih]

end add

section mul

noncomputable
def int.mul (a b: int) : int :=
  a.ind (fun _ => int) 0 (fun _ ih =>  ih + b) (fun _ ih =>  ih - b)
def int.mulFast (a b: int) : int := ofInt (a.toInt * b.toInt)

noncomputable
instance : Mul int := ⟨.mul⟩

def int.mul_sound : int.ind_sound (fun _ => int) 0 (fun _ ih =>  ih + b) (fun _ ih =>  ih - b) where
  zero_eq_succ := (sub_add_cancel _ _).symm
  succ_pred a := by
    simp
    rw [add_sub_cancel]
  pred_succ a := by
    simp
    rw [sub_add_cancel]

@[simp]
def int.zero_mul (a: int) : 0 * a = 0 := rfl
@[simp]
def int.neg_one_mul (a: int) : -1 * a = -a := rfl
@[simp]
def int.succ_mul (a b: int) : a.succ * b = a * b + b := by
  show mul _ _ = _
  apply int.ind_succ
  apply int.mul_sound
@[simp]
def int.pred_mul (a b: int) : a.pred * b = a * b - b := by
  show mul _ _ = _
  apply int.ind_pred
  apply int.mul_sound

@[csimp]
def int.mul_eq_mulFast : int.mul = int.mulFast := by
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
def int.mul_zero (a: int) : a * 0 = 0 := by
  induction a using ind with
  | zero => rfl
  | succ a ih => simp [ih]
  | pred a ih => simp [ih]

@[simp]
def int.mul_neg_one (a: int) : a * -1 = -a := by
  induction a using ind with
  | zero => rfl
  | succ a ih => simp [ih]
  | pred a ih => simp [ih]

@[simp]
def int.mul_succ (a b: int) : a * b.succ = a * b + a := by
  induction a using ind with
  | zero => rfl
  | succ a ih => simp [ih, add_assoc, add_comm a]
  | pred a ih => simp [ih, sub_eq_add_neg, add_assoc, add_comm a]

@[simp]
def int.mul_pred (a b: int) : a * b.pred = a * b - a := by
  induction a using ind with
  | zero => rfl
  | succ a ih => simp [ih, sub_eq_add_neg, add_assoc, add_comm b]
  | pred a ih => simp [ih, sub_eq_add_neg, add_assoc, add_comm (-a)]

def int.mul_comm (a b: int) : a * b = b * a := by
  induction a using ind with
  | zero => simp
  | succ a ih => simp [ih]
  | pred a ih => simp [ih]

def int.neg_mul_right (a b: int) : a * -b = -(a * b) := by
  induction a using ind with
  | zero => simp
  | succ a ih => simp [ih]
  | pred a ih => simp [ih, sub_eq_add_neg]

def int.neg_mul_left (a b: int) : -a * b = -(a * b) := by
  simp [mul_comm _ b, neg_mul_right]

@[simp]
def int.add_mul (a b k: int) : (a + b) * k = a * k + b * k := by
  induction k using ind with
  | zero => simp
  | succ k ih => simp [ih]; ac_rfl
  | pred k ih => simp [ih, sub_eq_add_neg]; ac_rfl

@[simp]
def int.mul_add (a b k: int) : k * (a + b) = k * a + k * b := by
  simp [mul_comm k]

@[simp]
def int.mul_sub (a b k: int) : k * (a - b) = k * a - k * b := by
  simp [mul_comm k, sub_eq_add_neg, neg_mul_left]

@[simp]
def int.sub_mul (a b k: int) : (a - b) * k = a * k - b * k := by
  simp [mul_comm _ k]

def int.mul_assoc (a b c: int) : a * b * c = a * (b * c) := by
  induction a using ind with
  | zero => simp
  | succ a ih => simp [ih]
  | pred a ih => simp [ih]

instance : @Std.Commutative int (· * ·) := ⟨int.mul_comm⟩
instance : @Std.Associative int (· * ·) := ⟨int.mul_assoc⟩

end mul
