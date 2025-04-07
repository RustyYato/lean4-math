import Math.Algebra.Hom.Defs
import Math.Algebra.Ring.Defs
import Math.Function.Basic
import Math.Data.Int.Basic

inductive BitInt.Pre where
| nil (b: Bool)
| cons (b: Bool) (bs: Pre)

inductive BitInt.Rel : BitInt.Pre -> BitInt.Pre -> Prop where
| nil b : Rel (.nil b) (.nil b)
| cons x as bs : Rel as bs -> Rel (.cons x as) (.cons x bs)
| nil_cons x as : Rel (.nil x) as -> Rel (.nil x) (.cons x as)
| cons_nil as x : Rel as (.nil x) -> Rel (.cons x as) (.nil x)

@[refl]
def BitInt.Rel.refl (a: BitInt.Pre) : BitInt.Rel a a := by
  induction a with
  | nil => exact .nil _
  | cons a as ih => exact ih.cons _ _ _

@[symm]
def BitInt.Rel.symm {as bs: BitInt.Pre} : BitInt.Rel as bs -> BitInt.Rel bs as := by
  intro h
  induction h with
  | nil => exact .nil _
  | cons x as bs ab ih => exact ih.cons _ _ _
  | nil_cons x as h ih => exact ih.cons_nil _ _
  | cons_nil x as h ih => exact ih.nil_cons _ _

def BitInt.Rel.trans {a b c: BitInt.Pre} : BitInt.Rel a b -> BitInt.Rel b c -> BitInt.Rel a c := by
  intro ab bc
  induction ab generalizing c with
  | nil => assumption
  | cons x as bs h ih =>
    cases bc
    apply Rel.cons
    apply ih
    assumption
    apply Rel.cons_nil
    apply ih
    assumption
  | nil_cons x as h ih =>
    cases bc
    apply Rel.nil_cons
    apply ih
    assumption
    exact .nil _
  | cons_nil as x h ih =>
    cases bc
    apply Rel.cons_nil
    apply ih
    exact .nil _
    apply Rel.cons
    apply ih
    assumption

instance BitInt.Pre.instSetoid : Setoid BitInt.Pre where
  r := BitInt.Rel
  iseqv := {
    refl := BitInt.Rel.refl
    symm := BitInt.Rel.symm
    trans := BitInt.Rel.trans
  }

@[refl]
def setoid_refl [h: Setoid α] (a: α) : a ≈ a := h.iseqv.refl _

@[symm]
def setoid_symm [h: Setoid α] (a b: α) : a ≈ b -> b ≈ a := h.iseqv.symm

def BitInt.decRelNil : ∀(x: Bool) (as: BitInt.Pre), Decidable (Rel (.nil x) as)
| true, .nil false
| false, .nil true
| true, .cons false _
| false, .cons true _ => .isFalse nofun

| true, .nil true
| false, .nil false => .isTrue (.nil _)
| true, .cons true as =>
  match decRelNil true as with
  | .isTrue h => .isTrue (h.nil_cons)
  | .isFalse h => .isFalse fun g => by
    cases g; contradiction
| false, .cons false as =>
  match decRelNil false as with
  | .isTrue h => .isTrue (h.nil_cons)
  | .isFalse h => .isFalse fun g => by
    cases g; contradiction

instance BitInt.decRel : ∀as bs: BitInt.Pre, Decidable (as ≈ bs)
| .nil false, .nil true
| .nil true, .nil false
| .nil false, .cons true _
| .nil true, .cons false _
| .cons false _, .cons true _
| .cons true _, .cons false _
| .cons false _, .nil true
| .cons true _, .nil false => .isFalse nofun
| .nil true, .nil true
| .nil false, .nil false => .isTrue (.nil _)
| .nil true, .cons true as
| .nil false, .cons false as => BitInt.decRelNil _ _
| .cons true as, .nil true =>
  match BitInt.decRelNil true (.cons true as) with
  | .isTrue h => .isTrue h.symm
  | .isFalse h => .isFalse fun g => h g.symm
| .cons false as, .nil false =>
  match BitInt.decRelNil false (.cons false as) with
  | .isTrue h => .isTrue h.symm
  | .isFalse h => .isFalse fun g => h g.symm
| .cons true as, .cons true bs
| .cons false as, .cons false bs =>
  match decRel as bs with
  | .isTrue h => .isTrue (h.cons _ _)
  | .isFalse h => .isFalse fun g => by
    cases g; contradiction

def BitInt := Quotient BitInt.Pre.instSetoid

namespace BitInt

instance : DecidableEq BitInt := Quotient.decidableEq

def mk : Pre -> BitInt := Quotient.mk _

scoped notation "⟦" x "⟧" => mk x

def sound {a b: Pre}: a ≈ b -> ⟦a⟧ = ⟦b⟧ := Quotient.sound
def exact {a b: Pre}: ⟦a⟧ = ⟦b⟧ -> a ≈ b := Quotient.exact

def trans { a b c: Pre } : a ≈ b -> b ≈ c -> a ≈ c :=
  BitInt.Pre.instSetoid.iseqv.trans

def rel_cons { x: Bool } { a b: Pre } : a ≈ b -> Pre.cons x a ≈ Pre.cons x b := Rel.cons x a b
def rel_nil_cons { x: Bool } { a: Pre } : .nil x ≈ a -> .nil x ≈ Pre.cons x a := Rel.nil_cons x a
def rel_cons_nil { x: Bool } { a: Pre } : a ≈ .nil x -> Pre.cons x a ≈ .nil x := Rel.cons_nil a x

def ind {motive: BitInt -> Prop} : (mk: ∀a, motive (mk a)) -> ∀a, motive a := Quotient.ind
def ind₂ {motive: BitInt -> BitInt -> Prop} : (mk: ∀a b, motive (mk a) (mk b)) -> ∀a b, motive a b := Quotient.ind₂
def ind₃ {motive: BitInt -> BitInt -> BitInt -> Prop} : (mk: ∀a b c, motive (mk a) (mk b) (mk c)) -> ∀a b c, motive a b c := by
  intro h a b c
  induction a, b using ind₂
  induction c using ind
  apply h
def ind₄ {motive: BitInt -> BitInt -> BitInt -> BitInt -> Prop} : (mk: ∀a b c d, motive (mk a) (mk b) (mk c) (mk d)) -> ∀a b c d, motive a b c d := by
  intro h a b c d
  induction a, b using ind₂
  induction c, d using ind₂
  apply h

def Pre.cons_if : Bool -> Pre -> Pre
| true, .nil true => .nil true
| false, .nil false => .nil false
| x, as' => .cons x as'

def Pre.minimize : Pre -> Pre := fun x =>
match x with
| .nil x => .nil x
| .cons x as => (Pre.minimize as).cons_if x

def Pre.cons_if_equiv (x: Bool) (a: Pre) : a.cons_if x ≈ (.cons x a) := by
  unfold cons_if
  cases x <;> cases a <;> (rename Bool => ax; cases ax)
  any_goals rfl
  apply Rel.nil_cons; rfl
  apply Rel.nil_cons; rfl

def Pre.minimize_equiv (a: Pre) : a.minimize ≈ a := by
  induction a with
  | nil x => rfl
  | cons x a ih =>
    unfold minimize
    apply trans
    apply cons_if_equiv
    apply Rel.cons
    assumption

def rep : BitInt -> Pre := by
  apply Quotient.lift Pre.minimize
  intro a b eq
  induction eq with
  | nil => rfl
  | cons x as bs h ih =>
    unfold Pre.minimize
    rw [ih]
  | nil_cons x as h ih =>
    unfold Pre.minimize
    rw [←ih]
    cases x <;> rfl
  | cons_nil as x h ih =>
    unfold Pre.minimize
    rw [ih]
    cases x <;> rfl

def rep_inj (a b: BitInt) : a.rep = b.rep ↔ a = b := by
  apply flip Iff.intro
  intro h; rw [h]
  intro h
  induction a, b using ind₂ with | mk a b =>
  replace h : a.minimize = b.minimize := h
  apply Quotient.sound
  apply trans (Pre.minimize_equiv _).symm
  apply trans _ (Pre.minimize_equiv _)
  rw [h]

def minimize : BitInt -> BitInt := by
  apply Quotient.lift (⟦Pre.minimize ·⟧)
  intro a b eq
  apply Quotient.sound
  apply trans (Pre.minimize_equiv _)
  apply trans _ (Pre.minimize_equiv _).symm
  assumption

@[simp]
def minimize_eq (a: BitInt) : a.minimize = a := by
  induction a using ind
  apply Quotient.sound
  apply Pre.minimize_equiv

def Pre.map (op: Bool -> Bool) : Pre -> Pre
| .nil x => .nil (op x)
| .cons a as => .cons (op a) (as.map op)

def Pre.map₂ (op: Bool -> Bool -> Bool) : Pre -> Pre -> Pre
| .nil x, .nil y => .nil (op x y)
| .nil x, .cons y ys => .cons (op x y) (Pre.map₂ op (.nil x) ys)
| .cons x xs, .nil y => .cons (op x y) (Pre.map₂ op xs (.nil y))
| .cons x xs, .cons y ys => .cons (op x y) (Pre.map₂ op xs ys)

def Pre.not := Pre.map Bool.not

def Pre.neg : Pre -> Pre
| .nil x =>
  match x with
  | false => .nil false
  | true => .cons true (.nil false)
| .cons a as =>
  .cons a <|
  match a with
  | true => as.not
  | false => as.neg

@[reducible]
def Pre.ofNat (n: Nat) : Pre :=
  if n = 0 then .nil false else .cons (n % 2 == 1) (Pre.ofNat (n / 2))

def ofNat (n: Nat) : BitInt := ⟦.ofNat n⟧

@[reducible]
def Pre.ofInt (n: Int) : Pre :=
  if n = 0 then .nil false else if n = -1 then .nil true else .cons (n % 2 == 1) (Pre.ofInt (n / 2))
termination_by n.natAbs

def ofInt (n: Int) : BitInt := ⟦.ofInt n⟧

instance : NatCast BitInt where
  natCast := ofNat
instance : IntCast BitInt where
  intCast := ofInt

def Pre.toInt : Pre -> Int
| .nil false => 0
| .nil true => -1
| cons false as => 2 * as.toInt
| cons true as => 2 * as.toInt + 1

def Pre.ofInt_toInt (n: Int) : (Pre.ofInt n).toInt = n := by
  induction n using Pre.ofInt.induct with
  | case1 | case2 => rfl
  | case3 x ne_zero ne_negone ih =>
    unfold ofInt
    rw [if_neg ne_zero, if_neg ne_negone]
    rcases Int.emod_two_eq_zero_or_one x with h | h
    rw [h]
    unfold toInt; dsimp
    rw [ih]
    exact Int.mul_ediv_cancel_of_emod_eq_zero h
    rw [h]
    unfold toInt; dsimp
    rw [ih]
    rw [←h, Int.ediv_add_emod]

def Pre.toInt_ofInt (n: Pre) : Pre.ofInt (Pre.toInt n) ≈ n := by
  induction n with
  | nil a => revert a; decide
  | cons a as ih =>
    cases a <;> unfold toInt ofInt
    split
    apply rel_nil_cons
    rename_i h
    rw [(Int.mul_eq_zero.mp h).resolve_left (by decide)] at ih
    exact ih
    rw [if_neg, Int.mul_emod_right, Int.mul_ediv_cancel_left]
    apply rel_cons
    assumption
    decide
    omega
    rw [if_neg]
    split
    apply rel_nil_cons
    rename_i h
    replace h : as.toInt = -1 := by omega
    rw [h] at ih
    assumption
    rw [Int.add_emod, Int.mul_emod_right]
    apply rel_cons
    rw [show (2 * as.toInt + 1) / 2 = as.toInt by omega]
    assumption
    omega

def Pre.ofInt_inj {a b: Int} : Pre.ofInt a = Pre.ofInt b ↔ a = b :=
  (Function.IsLeftInverse.Injective Pre.ofInt_toInt).eq_iff

def toInt : BitInt -> Int := by
  apply Quotient.lift Pre.toInt
  intro a b eq
  induction eq with
  | nil x => revert x; decide
  | cons x as bs h ih =>
    cases x <;> unfold Pre.toInt <;> congr
  | nil_cons x as h ih =>
    cases x <;> unfold Pre.toInt
    rw [←ih]
    rfl
    rw [←ih]
    rfl
  | cons_nil as x h ih =>
    cases x <;> unfold Pre.toInt
    rw [ih]
    rfl
    rw [ih]
    rfl

def intCast_toInt (n: Int) : (n: BitInt).toInt = n := Pre.ofInt_toInt _
def toInt_intCast (n: BitInt) : n.toInt = n := by
  cases n using ind with | mk n =>
  apply Quotient.sound
  apply Pre.toInt_ofInt n

def intCast_inj {a b: Int} : (a: BitInt) = (b: BitInt) ↔ a = b :=
  (Function.IsLeftInverse.Injective intCast_toInt).eq_iff
def toInt_inj {a b: BitInt} : a.toInt = b.toInt ↔ a = b :=
  (Function.IsLeftInverse.Injective toInt_intCast).eq_iff

instance : OfNat Pre n := ⟨.ofNat n⟩
instance : OfNat BitInt n := ⟨n⟩

def Pre.test_bit (x: Pre) (n: Nat) : Bool := match x with
| .nil x => x
| .cons x xs =>
  match n with
  | 0 => x
  | n + 1 => xs.test_bit n

instance : GetElem Pre Nat Bool (fun _ _ => True) where
  getElem b i _ := b.test_bit i

def Pre.equivIffTestBitEq {a b: Pre} : a ≈ b ↔ ∀i: Nat, a[i] = b[i] := by
  apply Iff.intro
  · intro eq i
    induction eq generalizing i with
    | nil => rfl
    | cons x as bs h ih =>
      cases i
      rfl
      apply ih
    | nil_cons x as h ih =>
      cases i with
      | zero => rfl
      | succ i => apply ih i
    | cons_nil as x h ih =>
      cases i with
      | zero => rfl
      | succ i => apply ih i
  · intro h
    induction a generalizing b with
    | nil a =>
      induction b generalizing a with
      | nil b => rw [show a = b from h 0]
      | cons b bs ih =>
        rw [←show a = b from h 0]
        apply rel_nil_cons
        apply ih
        intro i
        apply (h (i + 1)).trans
        rfl
    | cons a as ih =>
      cases b with
      | nil b =>
        rw [show a = b from h 0]
        apply rel_cons_nil
        apply ih
        intro i
        apply (h (i + 1)).trans
        rfl
      | cons b bs =>
        rw [show a = b from h 0]
        apply rel_cons
        apply ih
        intro i
        apply h (i + 1)

@[simp]
def Pre.test_bit_cons_succ (a: Bool) (as: Pre) (i: Nat) : (Pre.cons a as)[i + 1] = as[i] := rfl

@[simp]
def Pre.test_bit_map (f: Bool -> Bool) (a: Pre) (i: Nat) :
  (a.map f)[i] = f a[i] := by
  induction a generalizing i with
  | nil => rfl
  | cons a as ih =>
    cases i
    rfl
    simp [map]
    apply ih

@[simp]
def Pre.test_bit_map₂ (f: Bool -> Bool -> Bool) (a b: Pre) (i: Nat) :
  (a.map₂ f b)[i] = f a[i] b[i] := by
  induction a generalizing b i with
  | nil a =>
    induction b generalizing a i with
    | nil b =>
      unfold map₂
      rfl
    | cons b bs ih =>
      unfold map₂
      cases i
      rfl
      simp; apply ih
  | cons a as ih =>
    cases b with
    | nil b =>
      unfold map₂
      cases i
      rfl
      simp; apply ih
    | cons b bs =>
      unfold map₂
      cases i
      rfl
      simp; apply ih

def Pre.pred : Pre -> Pre
| .nil x =>
  match x with
  | false => .nil true
  | true => .cons false (.nil true)
| .cons x xs =>
  .cons (!x) (match x with
    | true => xs
    | false =>xs.pred)

def Pre.succ : Pre -> Pre
| .nil x =>
  match x with
  | false => .cons true (.nil false)
  | true => .nil false
| .cons x xs =>
  .cons (!x) (match x with
    | true => xs.succ
    | false =>xs)

def Pre.map.spec {f: Bool -> Bool} {a b: Pre} : a ≈ b -> a.map f ≈ b.map f := by
  intro eq
  apply equivIffTestBitEq.mpr
  intro i
  simp
  rw [equivIffTestBitEq.mp eq]

def Pre.map₂.spec {f: Bool -> Bool -> Bool} {a b c d: Pre} : a ≈ c -> b ≈ d -> a.map₂ f b ≈ c.map₂ f d := by
  intro ac bd
  apply equivIffTestBitEq.mpr
  intro i
  simp
  rw [equivIffTestBitEq.mp ac, equivIffTestBitEq.mp bd]

def Pre.pred.spec {a b: Pre} : a ≈ b -> a.pred ≈ b.pred := by
  intro eq
  induction eq with
  | nil => rfl
  | cons x as bs h ih =>
    cases x <;> apply rel_cons
    assumption
    assumption
  | nil_cons x as h ih =>
    cases x
    apply rel_nil_cons
    assumption
    apply rel_cons
    assumption
  | cons_nil as x h ih =>
    cases x
    apply rel_cons_nil
    assumption
    apply rel_cons
    assumption

def Pre.succ.spec {a b: Pre} : a ≈ b -> a.succ ≈ b.succ := by
  intro eq
  induction eq with
  | nil => rfl
  | cons x as bs h ih =>
    cases x <;> apply rel_cons
    assumption
    assumption
  | nil_cons x as h ih =>
    cases x
    apply rel_cons
    assumption
    apply rel_nil_cons
    assumption
  | cons_nil as x h ih =>
    cases x
    apply rel_cons
    assumption
    apply rel_cons_nil
    assumption

def Pre.neg.spec {a b: Pre} : a ≈ b -> a.neg ≈ b.neg := by
  intro h
  induction h with
  | nil => rfl
  | cons x as bs h ih =>
    cases x
    apply rel_cons
    assumption
    apply rel_cons
    apply Pre.map.spec
    assumption
  | nil_cons x as h ih =>
    cases x
    apply rel_nil_cons
    assumption
    apply rel_cons
    show (nil true).not ≈ _
    apply Pre.map.spec
    assumption
  | cons_nil as x h ih =>
    cases x
    apply rel_cons_nil
    assumption
    apply rel_cons
    show _ ≈ (nil true).not
    apply Pre.map.spec
    assumption

def map (f: Bool -> Bool) : BitInt -> BitInt := by
  apply Quotient.lift (⟦·.map f⟧)
  intro a b eq
  apply Quotient.sound
  apply Pre.map.spec
  assumption

def map₂ (f: Bool -> Bool -> Bool) : BitInt -> BitInt -> BitInt := by
  apply Quotient.lift₂ (⟦·.map₂ f ·⟧)
  intro a b c d ac bd
  apply Quotient.sound
  apply Pre.map₂.spec
  assumption
  assumption

def pred : BitInt -> BitInt := by
  apply Quotient.lift (⟦·.pred⟧)
  intro a b eq
  apply Quotient.sound
  apply Pre.pred.spec
  assumption

def succ : BitInt -> BitInt := by
  apply Quotient.lift (⟦·.succ⟧)
  intro a b eq
  apply Quotient.sound
  apply Pre.succ.spec
  assumption

def Pre.neg_spec_one (a: Pre) : Pre :=
  if a ≈ 1 then .nil true
  else a.neg

def neg : BitInt -> BitInt := by
  apply Quotient.lift (⟦·.neg_spec_one⟧)
  intro a b eq
  apply Quotient.sound
  unfold Pre.neg_spec_one
  split <;> rename_i h
  rw [if_pos]
  apply trans _ h; symm; assumption
  rw [if_neg]
  apply Pre.neg.spec
  assumption
  intro g
  apply h
  apply trans eq
  assumption

@[simp]
def pred_succ (x: BitInt) : x.pred.succ = x := by
  induction x using ind with | mk x =>
  apply Quotient.sound
  induction x with
  | nil x => revert x; decide
  | cons x xs ih =>
    cases x <;> apply rel_cons
    assumption
    rfl

@[simp]
def succ_pred (x: BitInt) : x.succ.pred = x := by
  induction x using ind with | mk x =>
  apply Quotient.sound
  induction x with
  | nil x => revert x; decide
  | cons x xs ih =>
    cases x <;> apply rel_cons
    rfl
    assumption

@[simp]
def succ_inj {a b: BitInt} : a.succ = b.succ ↔ a = b := by
  apply flip Iff.intro
  intro h; rw [h]
  intro h
  rw [←succ_pred a, ←succ_pred b, h]

@[simp]
def pred_inj {a b: BitInt} : a.pred = b.pred ↔ a = b := by
  apply flip Iff.intro
  intro h; rw [h]
  intro h
  rw [←pred_succ a, ←pred_succ b, h]

instance : Neg BitInt where
  neg := .neg

def not (x: BitInt) : BitInt := x.map Bool.not
def and (a b: BitInt) : BitInt := map₂ Bool.and a b
def or (a b: BitInt) : BitInt := map₂ Bool.or a b
def xor (a b: BitInt) : BitInt := map₂ Bool.xor a b

@[simp] def mk_succ (x: Pre) : (mk x).succ = mk x.succ := rfl
@[simp] def mk_pred (x: Pre) : (mk x).pred = mk x.pred := rfl
@[simp] def mk_map (f: Bool -> Bool) (x: Pre) : (mk x).map f = mk (x.map f) := rfl
@[simp] def mk_not (x: Pre) : (mk x).not = mk x.not := rfl
@[simp] def mk_neg (x: Pre) : -(mk x) = mk x.neg := by
  apply Quotient.sound
  unfold Pre.neg_spec_one
  split
  rename_i h
  apply flip trans
  apply Pre.neg.spec
  symm; assumption
  decide +kernel
  rfl

def test_bit (i: Nat) : BitInt -> Bool := by
  apply Quotient.lift (Pre.test_bit · i)
  intro a b eq
  apply Pre.equivIffTestBitEq.mp
  assumption

instance : GetElem BitInt Nat Bool (fun _ _ => True) where
  getElem x i _ := x.test_bit i

@[ext]
def ext (a b: BitInt) : (∀i: Nat, a[i] = b[i]) -> a = b := by
  intro h
  induction a, b using ind₂
  apply Quotient.sound
  apply Pre.equivIffTestBitEq.mpr
  assumption

@[simp]
def test_bit_map (f: Bool -> Bool) (a: BitInt) (i: Nat) :
  (a.map f)[i] = f a[i] := by
  induction a using ind
  apply Pre.test_bit_map

@[simp]
def test_bit_map₂ (f: Bool -> Bool -> Bool) (a b: BitInt) (i: Nat) :
  (a.map₂ f b)[i] = f a[i] b[i] := by
  induction a, b using ind₂
  apply Pre.test_bit_map₂

instance : AndOp BitInt := ⟨.and⟩
instance : OrOp BitInt := ⟨.or⟩
instance : Xor BitInt := ⟨.xor⟩

@[simp]
def test_bit_not (a: BitInt) (i: Nat) : a.not[i] = !a[i] := test_bit_map _ _ _
@[simp]
def test_bit_and (a b: BitInt) (i: Nat) : (a &&& b)[i] = (a[i] && b[i]) := test_bit_map₂ _ _ _ _
@[simp]
def test_bit_or (a b: BitInt) (i: Nat) : (a ||| b)[i] = (a[i] || b[i]) := test_bit_map₂ _ _ _ _
@[simp]
def test_bit_xor (a b: BitInt) (i: Nat) : (a ^^^ b)[i] = (a[i] ^^ b[i]) := test_bit_map₂ _ _ _ _

@[simp]
def not_not (a: BitInt) : a.not.not = a := by
  ext i; simp

@[simp]
def neg_neg (a: BitInt) : - -a = a := by
  induction a using ind with | mk a =>
  simp
  apply Quotient.sound
  induction a with
  | nil a => revert a; decide
  | cons a as ih =>
    cases a
    apply rel_cons
    assumption
    apply rel_cons
    apply Quotient.exact
    apply not_not ⟦as⟧

@[simp]
def not_inj {a b: BitInt} : a.not = b.not ↔ a = b := by
  apply Iff.intro
  intro h
  rw [←not_not a, ←not_not b, h]
  intro h; rw [h]
@[simp]
def neg_inj {a b: BitInt} : -a = -b ↔ a = b := by
  apply Iff.intro
  intro h
  rw [←neg_neg a, ←neg_neg b, h]
  intro h; rw [h]

def neg_eq_not_succ (a: BitInt) : -a = a.not.succ := by
  induction a using ind with | mk a =>
  simp
  apply Quotient.sound
  induction a with
  | nil a => revert a; decide
  | cons a as ih =>
    cases a
    apply rel_cons
    assumption
    apply rel_cons
    rfl

def neg_eq_pred_not (a: BitInt) : -a = a.pred.not := by
  conv => { rhs; rw [←neg_neg a, neg_eq_not_succ (-a)] }
  rw [succ_pred, not_not]

def not_eq_neg_pred (a: BitInt) : a.not = (-a).pred := by
  rw [neg_eq_not_succ, succ_pred]

def not_eq_succ_neg (a: BitInt) : a.not = -a.succ := by
  rw [neg_eq_pred_not, succ_pred]

def neg_succ_eq_pred_neg (a: BitInt) : -a.succ = (-a).pred := by
  rw [neg_eq_pred_not, succ_pred, not_eq_neg_pred]
def neg_pred_eq_succ_neg (a: BitInt) : -a.pred = (-a).succ := by
  apply neg_inj.mp
  rw [neg_neg, neg_succ_eq_pred_neg, neg_neg]

def Pre.ofNat_succ (n: Nat) : Pre.ofNat (n + 1) ≈ (Pre.ofNat n).succ := by
  unfold ofNat
  rw [if_neg]
  split
  subst n
  rfl
  rw [Nat.add_mod]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  rw [h]
  apply rel_cons
  rw [←Nat.div_add_mod n 2, h, Nat.add_zero, Nat.mul_add_div, Nat.mul_add_div]
  rfl
  decide
  decide
  rw [h]
  apply rel_cons
  conv => { lhs; rw [←Nat.div_add_mod n 2] }
  rw [h, Nat.add_assoc, Nat.mul_add_div]
  apply ofNat_succ
  decide
  intro
  contradiction

def Pre.ofNat_pred (n: Nat) : (Pre.ofNat (n + 1)).pred ≈ Pre.ofNat n := by
  apply Rel.trans
  apply pred.spec
  apply ofNat_succ
  show (_: Pre) ≈ _
  apply Quotient.exact
  show (mk _).succ.pred = (mk _)
  rw [succ_pred]

def ofNat_succ (n: Nat) : ofNat (n + 1) = (ofNat n).succ := by
  apply Quotient.sound
  apply Pre.ofNat_succ

def ofNat_pred (n: Nat) : (ofNat (n + 1)).pred = ofNat n := by
  apply Quotient.sound
  apply Pre.ofNat_pred

def equiv_nat_or_neg_succ_nat (b: BitInt) : (∃n: Nat, b = ofNat n) ∨ (∃n: Nat, b = -ofNat (n + 1)) := by
  induction b using ind with | mk b =>
  induction b with
  | nil b =>
    cases b
    left; exists 0
    right; exists 0
  | cons b bs ih =>
    rcases ih with ⟨n, h⟩ | ⟨n, h⟩
    · left
      replace h := Quotient.exact h
      cases b
      · exists 2 * n
        apply Quotient.sound
        rw [Pre.ofNat]
        cases n
        rw [if_pos rfl]
        apply rel_cons_nil
        assumption
        rw [if_neg]
        rw [Nat.mul_mod_right]
        apply rel_cons
        rw [Nat.mul_div_right]
        assumption
        decide
        rw [Nat.mul_add]
        intro; contradiction
      · exists 2 * n + 1
        apply Quotient.sound
        rw [Pre.ofNat]
        rw [if_neg, Nat.mul_add_mod]
        apply rel_cons
        erw [Nat.mul_add_div, Nat.add_zero]
        assumption
        decide
        intro; contradiction
    · replace h: ⟦bs⟧ = -(mk _) := h
      rw [mk_neg] at h
      replace h := Quotient.exact h
      right
      show ∃n, _ = -(mk _)
      conv => { arg 1; intro n; rw [mk_neg] }
      cases b
      exists 2 * n + 1
      apply Quotient.sound
      unfold Pre.ofNat
      rw [if_neg, Nat.add_assoc, Nat.mul_add_mod, Nat.mul_add_div]
      show _ ≈ Pre.neg (Pre.cons false (Pre.ofNat (n + 1)))
      apply rel_cons
      assumption
      decide
      intro; contradiction
      exists 2 * n
      apply Quotient.sound
      rw [Pre.ofNat]
      rw [if_neg, Nat.mul_add_mod, Nat.mul_add_div]
      apply rel_cons
      · apply Quotient.exact
        show (mk _) = (mk _).not
        rw [not_eq_succ_neg, mk_succ, mk_neg]
        apply Quotient.sound
        apply h.trans
        show _ ≈ (_: Pre)
        apply Pre.neg.spec
        show _ ≈ (Pre.ofNat n).succ
        apply Pre.ofNat_succ
      decide
      intro h; contradiction

@[induction_eliminator]
def induction
  {motive: BitInt -> Prop}
  (zero: motive 0)
  (pred: ∀i, motive i -> motive i.pred)
  (succ: ∀i, motive i -> motive i.succ): ∀i, motive i := by
  intro i
  rcases equiv_nat_or_neg_succ_nat i with ⟨n, h⟩ | ⟨n, h⟩ <;> subst i
  · induction n with
    | zero => apply zero
    | succ n ih =>
      rw [ofNat_succ]
      apply succ
      assumption
  · rw [ofNat_succ, neg_succ_eq_pred_neg]
    apply pred
    induction n with
    | zero => assumption
    | succ n ih =>
      rw [ofNat_succ, neg_succ_eq_pred_neg]
      apply pred
      assumption

def Pre.pred_if (x: Pre) : Bool -> Pre
| false => x
| true => pred x

def Pre.succ_if (x: Pre) : Bool -> Pre
| false => x
| true => succ x

def Pre.nil_add_with_carry (b: Pre) (a c: Bool) :=
  match a with
  | true => b.pred_if (!c)
  | false => b.succ_if c

private
def at_least_two_bits_set : ∀(_ _ _: Bool), Bool
| true, true, true
| true, true, false
| true, false, true
| false, true, true => true

| false, false, false
| false, false, true
| false, true, false
| true, false, false => false

def Pre.add_with_carry (a b: Pre) (c: Bool) : Pre :=
  match a with
  | .nil a => b.nil_add_with_carry a c
  | .cons a as =>
    match b with
    | .nil b => (Pre.cons a as).nil_add_with_carry b c
    | .cons b bs => .cons ((a ^^ b) ^^ c) (add_with_carry as bs (at_least_two_bits_set a b c))

def Pre.add (a b: Pre) : Pre := a.add_with_carry b false

def Pre.succ_if.spec (a b: Pre) : a ≈ b -> a.succ_if x ≈ b.succ_if x := by
  intro h
  unfold succ_if
  split
  assumption
  apply succ.spec
  assumption

def Pre.pred_if.spec (a b: Pre) : a ≈ b -> a.pred_if x ≈ b.pred_if x := by
  intro h
  unfold pred_if
  split
  assumption
  apply pred.spec
  assumption

def Pre.nil_add_with_carry.spec (a b: Pre) : a ≈ b -> a.nil_add_with_carry x y ≈ b.nil_add_with_carry x y := by
  intro h
  unfold nil_add_with_carry
  split
  apply pred_if.spec
  assumption
  apply succ_if.spec
  assumption

private
def Pre.add_with_carry.zero_right (a: Pre) : a.add_with_carry 0 false ≈ a := by
  unfold add_with_carry
  cases a with
  | nil a => revert a; decide
  | cons a as => rfl

private
def Pre.add_with_carry.zero_right' (a: Pre) : a.add_with_carry 0 true ≈ a.succ := by
  unfold add_with_carry
  cases a with
  | nil a => revert a; decide
  | cons a as => rfl

private
def Pre.add_with_carry.neg_one_right (a: Pre) : a.add_with_carry (Pre.nil true) true ≈ a := by
  unfold add_with_carry
  cases a with
  | nil a => revert a; decide
  | cons a as => rfl

private
def Pre.add_with_carry.neg_one_right' (a: Pre) : a.add_with_carry (Pre.nil true) false ≈ a.pred := by
  unfold add_with_carry
  cases a with
  | nil a => revert a; decide
  | cons a as => rfl

private
def Pre.succ_if_false (a: Pre) : a.succ_if false = a := rfl
private
def Pre.pred_if_false (a: Pre) : a.pred_if false = a := rfl

def Rel.symm_induction {motive: ∀{as bs: Pre}, as ≈ bs -> Prop}
  (nil: ∀a, motive (Rel.nil a))
  (cons: ∀a as bs (h: as ≈ bs), motive h -> motive (Rel.cons a _ _ h))
  (nil_cons: ∀a bs (h: Pre.nil a ≈ bs), motive h -> motive (Rel.nil_cons a _ h))
  (symm: ∀(as bs: Pre) (h: as ≈ bs), motive h.symm -> motive h)
  : ∀{as bs} (h: as ≈ bs), motive h := by
  intro as bs h
  induction h with
  | nil => apply nil
  | cons => apply cons; assumption
  | nil_cons => apply nil_cons; assumption
  | cons_nil b ds h =>
    apply symm
    apply nil_cons
    apply symm
    assumption
    symm
    assumption

def Rel.symm_induction' {motive: ∀{as bs: Pre}, as ≈ bs -> Prop}
  (nil: ∀a, motive (Rel.nil a))
  (cons: ∀a as bs (h: as ≈ bs), motive h -> motive (Rel.cons a _ _ h))
  (cons_nil: ∀a bs (h: bs ≈ Pre.nil a), motive h -> motive (Rel.cons_nil _ _ h))
  (symm: ∀(as bs: Pre) (h: as ≈ bs), motive h.symm -> motive h)
  : ∀{as bs} (h: as ≈ bs), motive h := by
  intro as bs h
  induction h with
  | nil => apply nil
  | cons => apply cons; assumption
  | cons_nil => apply cons_nil; assumption
  | nil_cons ds b h =>
    apply symm
    apply cons_nil
    apply symm
    assumption
    symm
    assumption

def Pre.add_with_carry.spec (a b c d: Pre) : a ≈ c -> b ≈ d -> a.add_with_carry b x ≈ c.add_with_carry d x := by
  intro ac bd
  induction ac using Rel.symm_induction generalizing b d x with
  | nil a =>
    apply nil_add_with_carry.spec
    assumption
  | cons a as cs ac ih =>
    cases bd with
    | nil b =>
      apply nil_add_with_carry.spec
      apply rel_cons
      assumption
    | cons b bs ds bd =>
      apply rel_cons
      apply ih
      assumption
    | nil_cons b ds bd =>
      cases a <;> cases b <;> cases x
      all_goals apply rel_cons
      any_goals
        apply flip Rel.trans
        apply ih
        assumption
        apply (Pre.add_with_carry.zero_right _).symm
      any_goals
        apply flip Rel.trans
        apply ih _ _ bd
        apply (Pre.add_with_carry.neg_one_right as).symm
      · apply flip Rel.trans
        apply ih _ _ bd
        apply (Pre.add_with_carry.neg_one_right' as).symm
      · apply flip Rel.trans
        apply ih _ _ bd
        apply (Pre.add_with_carry.zero_right' as).symm
    | cons_nil bs d bd =>
      cases a <;> cases d <;> cases x
      all_goals apply rel_cons
      any_goals
        apply Rel.trans
        apply ih
        assumption
        apply (Pre.add_with_carry.zero_right _)
      any_goals
        apply Rel.trans
        apply ih _ _ bd
        apply (Pre.add_with_carry.neg_one_right _)
      · apply Rel.trans
        apply ih _ _ bd
        apply (Pre.add_with_carry.neg_one_right' _)
      · apply Rel.trans
        apply ih _ _ bd
        apply (Pre.add_with_carry.zero_right' _)
  | nil_cons a cs ac ih =>
    cases bd with
    | nil b =>
      unfold add_with_carry nil_add_with_carry
      cases a <;> cases b <;> cases x
      any_goals apply succ_if.spec
      any_goals apply pred_if.spec
      all_goals apply rel_nil_cons
      any_goals assumption
      apply flip Rel.trans
      apply pred.spec
      assumption
      rfl
      apply flip Rel.trans
      apply succ.spec
      assumption
      rfl
    | cons b bs ds bd =>
      cases a <;> cases b <;> cases x
      all_goals
        apply rel_cons
        apply flip Rel.trans
        apply ih _ _ bd
        rfl
    | nil_cons d bs bd =>
      cases a <;> cases d <;> cases x
      any_goals apply rel_cons
      any_goals apply rel_nil_cons
      all_goals apply Rel.trans _ (ih _ _ bd)
      all_goals rfl
    | cons_nil ds b bd =>
      cases a <;> cases b <;> cases x
      all_goals apply rel_cons
      any_goals apply bd.trans
      any_goals assumption
      any_goals apply Rel.trans _ ac
      any_goals apply Rel.symm (bs := nil _)
      apply Rel.trans
      apply pred.spec ac.symm
      rfl
      apply Rel.trans
      apply succ.spec bd
      rfl
      apply Rel.trans
      apply pred.spec bd
      rfl
      apply Rel.trans
      apply succ.spec ac.symm
      rfl
  | symm _ _ _ ih =>
    symm
    apply ih
    symm
    assumption

def Pre.add.spec (a b c d: Pre) : a ≈ c -> b ≈ d -> a.add b ≈ c.add d := by
  apply Pre.add_with_carry.spec

instance : Add BitInt where
  add := by
    apply Quotient.lift₂ (⟦·.add ·⟧)
    intro a b c d ac bd
    apply Quotient.sound
    apply Pre.add.spec
    assumption
    assumption

@[simp]
def mk_add (a b: Pre) : (mk a) + (mk b) = mk (a.add b) := rfl

def altbs_comm: BitInt.at_least_two_bits_set a b c = BitInt.at_least_two_bits_set b a c := by
  revert a b c; decide

def add_with_carry_eqv_add (a b: Pre) (c: Bool) : a.add_with_carry b c ≈ (a.add b).succ_if c := by
  cases c
  rfl
  induction a generalizing b with
  | nil a =>
    unfold Pre.add Pre.add_with_carry
    cases a <;> unfold Pre.nil_add_with_carry
    rfl
    symm
    apply Quotient.exact
    apply pred_succ ⟦b⟧
  | cons a as ih =>
    cases b with
    | nil b =>
      cases b
      rfl
      apply Quotient.exact
      symm
      apply pred_succ ⟦Pre.cons _ _⟧
    | cons b s =>
      unfold Pre.add Pre.add_with_carry Pre.nil_add_with_carry Pre.pred_if Pre.succ_if
      dsimp
      unfold Pre.succ
      rw [Bool.xor_false, Bool.xor_true]
      apply rel_cons
      cases a <;> cases b <;> simp [at_least_two_bits_set]
      rfl
      apply ih
      apply ih
      rfl

instance : IsAddCommMagma BitInt where
  add_comm := by
    intro a b
    cases a, b using ind₂ with | mk a b =>
    simp
    apply Quotient.sound
    induction a generalizing b with
    | nil a =>
      cases b with
      | nil b => revert a b; decide
      | cons b bs =>
        rfl
    | cons a as ih =>
      cases b
      rfl
      unfold Pre.add Pre.add_with_carry
      dsimp
      rw [Bool.xor_comm a]
      apply rel_cons
      apply (add_with_carry_eqv_add _ _ _).trans
      apply Rel.trans _ (add_with_carry_eqv_add _ _ _).symm
      rw [altbs_comm]
      apply Pre.succ_if.spec
      apply ih

instance : IsAddZeroClass BitInt where
  zero_add a := by
    cases a using Quotient.ind
    rfl
  add_zero a := by
    rw [add_comm]
    cases a using Quotient.ind
    rfl

def succ_add (a b: BitInt) : a.succ + b = (a + b).succ := by
  cases a, b using ind₂ with | mk a b =>
  simp
  apply Quotient.sound
  induction a generalizing b with
  | nil a =>
    cases b with
    | nil b => revert a b; decide
    | cons b bs =>
      cases a <;> cases b
      any_goals rfl
      show Pre.cons false bs ≈ _
      apply Quotient.exact
      show mk _ = mk _
      rw [←mk_succ]
      apply pred_inj.mp
      rw [succ_pred]
      rfl
  | cons a as ih =>
    cases b with
    | nil b =>
      cases a <;> cases b
      any_goals rfl
      apply rel_cons
      apply Quotient.exact
      symm; apply pred_succ ⟦as⟧
      apply rel_cons
      simp
      apply Quotient.exact
      apply succ_pred ⟦as⟧
    | cons b bs =>
      cases a <;> cases b
      all_goals apply rel_cons
      rfl
      apply add_with_carry_eqv_add
      apply ih
      simp
      apply flip Rel.trans
      symm; apply add_with_carry_eqv_add
      apply ih
def add_succ (a b: BitInt) : a + b.succ = (a + b).succ := by
  rw [add_comm, succ_add, add_comm]
def pred_add (a b: BitInt) : a.pred + b = (a + b).pred := by
  apply succ_inj.mp
  rw [←succ_add, pred_succ, pred_succ]
def add_pred (a b: BitInt) : a + b.pred = (a + b).pred := by
  rw [add_comm, pred_add, add_comm]

instance : IsAddSemigroup BitInt where
  add_assoc a b c := by
    induction a with
    | zero => rw [zero_add, zero_add]
    | succ a ih => simp [succ_add, ih]
    | pred a ih => simp [pred_add, ih]

instance : SMul ℕ BitInt where
  smul := nsmulRec
instance : SMul ℤ BitInt where
  smul := zsmulRec
instance : Sub BitInt where
  sub a b := a + -b

instance : IsAddGroupWithOne BitInt where
  zero_add := zero_add
  add_zero := add_zero

  sub_eq_add_neg _ _ := rfl
  zsmul_ofNat _ _ := rfl
  zsmul_negSucc _ _ := rfl

  neg_add_cancel a := by
    induction a with
    | zero => rfl
    | succ a ih => rw [neg_succ_eq_pred_neg, pred_add, add_succ, succ_pred, ih]
    | pred a ih => rw [neg_pred_eq_succ_neg, succ_add, add_pred, pred_succ, ih]

  natCast_zero := rfl
  natCast_succ n := by
    show _ = _ + succ 0
    rw [add_succ, add_zero]
    exact ofNat_succ _

  intCast_ofNat n := by
    apply Quotient.sound
    induction n using Pre.ofNat.induct with
    | case1 => rfl
    | case2 x nz ih =>
      unfold Pre.ofInt Pre.ofNat
      rw [if_neg, if_neg, if_neg nz]
      show Pre.cons (x % ((2: Nat): Int) == ((1: Nat): Int)) _ ≈ _
      rw [←Int.ofNat_emod]
      rcases Nat.mod_two_eq_zero_or_one x with h | h
      rw [h]
      apply rel_cons
      assumption
      rw [h]
      apply rel_cons
      assumption
      omega
      omega
  intCast_negSucc n := by
    show mk _ = -mk _
    simp
    apply Quotient.sound
    induction n using Pre.ofNat.induct with
    | case1 => decide
    | case2 x nz ih =>
      unfold Pre.ofInt Pre.ofNat
      rw [if_neg]
      split
      rw [if_neg]
      rename_i h
      cases h
      contradiction
      omega
      show Pre.cons (_ % ((2: Nat): Int) == ((1: Nat): Int)) _ ≈ _
      rw [Int.negSucc_emod, ←Int.ofNat_emod, Nat.add_mod]
      rcases Nat.mod_two_eq_zero_or_one x with h | h
      rw [h]
      dsimp; apply rel_cons
      apply Quotient.exact
      show mk _ = mk _
      rw [←mk_not, not_eq_succ_neg]
      simp
      apply Quotient.sound
      apply ih.trans
      apply Pre.neg.spec
      apply (Pre.ofNat_succ _).trans
      apply Pre.succ.spec
      conv => {
        rhs; rw [←Nat.div_add_mod x 2, h, Nat.add_assoc, Nat.mul_add_div (by decide)]
      }
      rfl
      rw [h]
      apply rel_cons
      apply ih.trans
      apply Pre.neg.spec
      conv => {
        rhs; rw [←Nat.div_add_mod x 2, h, Nat.add_assoc, Nat.mul_add_div (by decide)]
      }
      decide
      omega

def Pre.nil_mul (b: Pre) : Bool -> Pre
| false => 0
| true => b.neg

def Pre.select (b: Pre) : Bool -> Pre
| false => 0
| true => b

def Pre.mul (a b: Pre) : Pre :=
  match a with
  | nil a => b.nil_mul a
  | cons a as =>
    match b with
    | nil b => (cons a as).nil_mul b
    | cons b bs => .cons (a && b) <| (bs.select a) |>.add (as.select b) |>.add (cons false <| (Pre.mul as bs))

def Pre.nil_mul.spec {a b: Pre} : a ≈ b -> a.nil_mul x ≈ b.nil_mul x := by
  intro eq
  cases x
  rfl
  apply neg.spec
  assumption

def Pre.select.spec {a b: Pre} : a ≈ b -> a.select x ≈ b.select x := by
  intro eq
  cases x
  rfl
  assumption

instance : Repr Pre where
  reprPrec p := reprPrec p.toInt

def Pre.add_self (a: Pre) : a.add a ≈ .cons false a := by
  induction a with
  | nil a =>  revert a; decide
  | cons a as ih =>
    cases a
    apply rel_cons
    apply ih
    apply rel_cons
    apply (add_with_carry_eqv_add _ _ _).trans
    show Pre.succ _ ≈ _
    apply Rel.trans
    apply succ.spec
    assumption
    rfl

def add_self' (a: Pre) : mk a + mk a = mk (.cons false a) := by
  apply Quotient.sound
  apply Pre.add_self

-- def Pre.mul_zero : ∀as: Pre, as.mul (nil false) = 0 := by
--   intro as
--   cases as; rename_i a
--   cases a
--   all_goals rfl
-- def Pre.mul_negone : ∀as: Pre, as.mul (nil true) = as.neg := by
--   intro as
--   cases as; rename_i a
--   cases a
--   all_goals rfl

@[simp]
def mk_zero : mk 0 = 0 := rfl

def Pre.induction {motive: Pre -> Prop}
  (zero: motive 0)
  (succ: ∀a, motive a -> motive a.succ)
  (pred: ∀a, motive a -> motive a.pred)
  (eqv: ∀a b, a ≈ b -> motive a -> motive b):
  ∀a, motive a := by
  intro a
  generalize ha':mk a =a'
  induction a' generalizing a with
  | zero =>
    apply eqv
    exact (exact ha').symm
    assumption
  | succ a ih =>
    rw [←pred_succ (mk a), succ_inj] at ha'
    have := ih _ ha'
    apply eqv _ _ _ (succ _ (ih _ ha'))
    apply exact
    apply pred_succ (mk a )
  | pred a ih =>
    rw [←succ_pred (mk a), pred_inj] at ha'
    have := ih _ ha'
    apply eqv _ _ _ (pred _ (ih _ ha'))
    apply exact
    apply succ_pred (mk a )

attribute [local simp] add_zero zero_add neg_add_cancel add_neg_cancel mul_zero zero_mul mul_one one_mul

def Pre.zero_mul (a: Pre) : mul 0 a ≈ 0 := by rfl
def Pre.negone_mul (a: Pre) : mul (nil true) a ≈ a.neg := by rfl
def Pre.one_mul (a: Pre) : mul 1 a ≈ a := by
  cases a with
  | nil a => revert a; decide
  | cons a as =>
    show mul (cons true (nil false)) _ ≈ _
    unfold mul
    dsimp
    rw [Bool.true_and, select]
    apply rel_cons
    apply exact
    simp [←mk_add, ←add_self', mul, nil_mul]
    cases a
    apply add_zero
    apply add_zero
def Pre.succ_mul (a b: Pre) : mul a.succ b ≈ (mul a b).add b := by
  induction a generalizing b with
  | nil a =>
    cases a
    · cases b with
      | nil b => cases b <;> decide
      | cons b bs =>
        simp [mul, nil_mul]
        unfold succ mul
        simp [select]
        apply rel_cons
        cases b <;> dsimp
        apply exact
        simp [←mk_add, ←add_self', sound (zero_mul _), show (nil false) = 0 from rfl]
        apply exact
        simp [←mk_add, ←add_self', sound (zero_mul _), show (nil false) = 0 from rfl]
    . show 0 ≈ _
      apply exact
      simp [←mk_add, sound (negone_mul _), ←mk_neg]
  | cons a as ih =>
    cases b with
    | nil b =>
      unfold succ mul
      cases b
      rfl
      simp [nil_mul]
      apply rel_cons
      cases a <;> simp
      all_goals apply exact
      rw [←mk_pred, ←mk_neg, ←mk_not]
      apply not_eq_neg_pred
      rw [←mk_neg, ←mk_succ, ←mk_not]
      symm; apply not_eq_succ_neg
    | cons b bs =>
      unfold add add_with_carry succ mul
      cases b <;> simp
      apply rel_cons
      rw [at_least_two_bits_set, ←add]
      cases a <;> simp
      unfold select; simp
      apply exact
      simp [←mk_add, add_comm]
      unfold select
      apply exact
      simp [←mk_add, ←add_self']
      rw [sound (ih bs)]
      simp [←mk_add]
      ac_rfl
      cases a <;> simp
      apply rel_cons
      rw [at_least_two_bits_set, ←add]
      apply exact
      simp [select, ←mk_add, ←add_self']
      ac_rfl
      apply rel_cons
      rw [at_least_two_bits_set]
      apply exact
      rw [sound (add_with_carry_eqv_add _ _ _), succ_if]
      simp [select, ←mk_add, ←add_self', sound (ih _), ←mk_succ, succ_add, add_succ]
      ac_rfl
def Pre.pred_mul (a b: Pre) : mul a.pred b ≈ (mul a b).add b.neg := by
  induction a generalizing b with
  | nil a =>
    cases a
    · cases b with
      | nil b => cases b <;> decide
      | cons b bs =>
        simp [mul, nil_mul]
        unfold pred neg mul nil_mul
        simp [select]
        apply rel_cons
        cases b <;> dsimp
        apply exact
        simp [←mk_add, ←add_self', sound (zero_mul _), show (nil false) = 0 from rfl]
        apply exact
        simp [←mk_add, ←add_self', sound (zero_mul _), show (nil false) = 0 from rfl]
    . show (cons false (nil true)).mul _ ≈ b.neg.add b.neg
      apply Rel.trans _ (add_self _).symm
      show _ ≈ (_: Pre)
      cases b with
      | nil b => cases b <;> decide
      | cons b bs =>
        apply rel_cons
        simp [select]
        cases b <;> simp
        apply exact
        simp [←mk_add, ←add_self', sound (negone_mul _)]
        rw [add_self']
        rfl
        apply exact
        simp [←mk_add, ←add_self', sound (negone_mul _)]
        rw [add_self']
        show BitInt.pred 0 + _ = _
        rw [pred_add, zero_add, ←mk_neg]
        show _ = -⟦cons false bs⟧.succ
        rw [neg_succ_eq_pred_neg, mk_neg]
        rfl
  | cons a as ih =>
    cases b with
    | nil b =>
      unfold pred mul
      cases b
      rfl
      simp [nil_mul]
      cases a
      all_goals
        apply rel_cons
        simp [at_least_two_bits_set]
        apply exact
        rw [sound (add_with_carry_eqv_add _ _ _), succ_if]
      show ⟦_⟧.pred.not = _
      rw [←neg_eq_pred_not, mk_neg, ←mk_add,
        show ⟦nil false⟧ = 0 by rfl, add_zero]
      rw [←mk_succ, ←mk_add, ←mk_not, ←succ_add,
        ←neg_eq_not_succ, mk_neg,
        show ⟦nil false⟧ = 0 by rfl, add_zero]
    | cons b bs =>
      unfold add add_with_carry pred mul
      cases b <;> simp
      apply rel_cons
      rw [at_least_two_bits_set, ←add]
      cases a <;> simp
      unfold select; simp
      apply exact
      simp [←mk_add, add_comm, ←add_self', sound (ih _)]
      rw [←mk_neg, add_comm _ (-⟦bs⟧), ←add_assoc, ←add_assoc, ←add_assoc,
        add_neg_cancel, zero_add]
      ac_rfl
      apply exact
      simp [select, ←mk_add, ←add_self']
      rw [add_comm ⟦bs⟧, add_assoc, ←mk_neg, add_neg_cancel, add_zero]
      cases a <;> apply rel_cons
      simp [select, at_least_two_bits_set]
      rw [←add]
      apply exact
      simp [←mk_add, ←add_self', sound (ih _),
        ←mk_not, ←mk_neg, not_eq_neg_pred, ←mk_pred, pred_add, add_pred]
      rw [add_comm ⟦bs⟧, add_assoc, add_comm _ (-⟦bs⟧), ←add_assoc ⟦bs⟧, ←add_assoc ⟦bs⟧,
        add_neg_cancel, zero_add]
      ac_rfl
      simp [select, at_least_two_bits_set]
      apply exact
      simp [sound (add_with_carry_eqv_add _ _ _), succ_if, ←mk_add,
        ←mk_succ, ←mk_not, ←add_self', ←add_succ]
      rw [←neg_eq_not_succ, add_assoc ⟦bs⟧, add_comm ⟦bs⟧, add_assoc, add_neg_cancel, add_zero]

def Pre.mul_comm (a b: Pre) : mul a b ≈ mul b a := by
  induction a generalizing b with
  | nil a =>
    cases b with
    | nil b => cases a <;> cases b <;> rfl
    | cons b bs =>
      cases a <;> rfl
  | cons a as ih =>
    cases b with
    | nil b => cases b <;> rfl
    | cons b bs =>
      unfold mul <;> dsimp
      rw [Bool.and_comm]
      apply rel_cons
      apply add.spec
      apply exact
      simp [←mk_add]
      rw [add_comm]
      apply rel_cons
      apply ih

def Pre.mul_zero (a: Pre) : mul a 0 ≈ 0 := by apply mul_comm
def Pre.mul_negone (a: Pre) : mul a (nil true) ≈ a.neg := by apply mul_comm
def Pre.mul_one (a: Pre) : mul a 1 ≈ a := by
  apply (mul_comm _ _).trans
  apply one_mul
def Pre.mul_succ (a b: Pre) : mul a b.succ ≈ (mul a b).add a := by
  apply (mul_comm _ _).trans
  apply (succ_mul _ _).trans
  apply add.spec
  apply mul_comm
  rfl
def Pre.mul_pred (a b: Pre) : mul a b.pred ≈ (mul a b).add a.neg := by
  apply (mul_comm _ _).trans
  apply (pred_mul _ _).trans
  apply add.spec
  apply mul_comm
  rfl

def Pre.mul.spec' {a b k: Pre} : a ≈ b -> a.mul k ≈ b.mul k := by
  intro ab
  induction ab using Rel.symm_induction generalizing k with
  | symm _ _ _ ih  => exact ih.symm
  | nil => rfl
  | cons a as bs ab ih =>
    cases k with
    | nil k =>
      dsimp [mul, nil_mul]
      cases k
      rfl
      apply neg.spec
      apply rel_cons
      assumption
    | cons k ks =>
      apply rel_cons
      apply exact
      simp [←mk_add, sound (select.spec ab), ←add_self', sound (ih )]
  | nil_cons a bs ab ih =>
    cases k with
    | nil k =>
      simp [mul, nil_mul]
      cases a <;> cases k
      rfl
      apply rel_nil_cons
      simp
      apply flip Rel.trans
      apply neg.spec; assumption
      rfl
      rfl
      apply flip Rel.trans
      apply rel_cons
      apply Pre.map.spec; assumption
      rfl
    | cons k ks =>
      simp [mul, nil_mul]
      cases a
      simp
      apply rel_nil_cons
      rw [select]
      apply exact
      simp [←mk_add, ←add_self', ←sound (select.spec ab), ←sound ih,
        show nil false = 0 from rfl, sound (zero_mul _)]
      cases k <;> rfl
      apply rel_cons
      apply exact
      simp [←mk_add, ←add_self', ←sound (select.spec ab), ←sound ih,
        show nil false = 0 from rfl, sound (zero_mul _)]
      rw [select, sound (negone_mul _)]
      cases k
      dsimp
      rw [select, mk_zero, add_zero, ←add_assoc, ←mk_neg, add_neg_cancel, zero_add]
      dsimp
      rw [add_comm ⟦ks⟧, ←add_assoc, add_assoc _ ⟦ks⟧, ←mk_neg, add_neg_cancel, add_zero]
      show ⟦ks⟧.not = BitInt.pred 0 + _
      rw [pred_add, zero_add, not_eq_neg_pred]

def Pre.mul.spec {a b c d: Pre} : a ≈ c -> b ≈ d -> a.mul b ≈ c.mul d := by
  intro ac bd
  induction a using Pre.induction generalizing b c d with
  | eqv a a' ha' ih =>
    apply flip Rel.trans
    apply ih
    apply ha'.trans
    assumption
    assumption
    apply Pre.mul.spec'
    symm; assumption
  | zero =>
    apply (zero_mul _).trans
    show (0: Pre) ≈ _
    clear bd
    induction c generalizing d with
    | nil c =>
      cases ac
      rfl
    | cons c cs ih =>
      cases ac
      cases d with
      | nil d =>
        cases d
        rfl
        apply rel_nil_cons
        simp
        apply flip Rel.trans
        apply neg.spec
        assumption
        rfl
      | cons d ds =>
        rename_i ac
        apply rel_nil_cons
        apply exact
        simp [select, ←mk_add, ←add_self', ←sound (ih ac)]
        cases d
        rfl
        apply sound; assumption
  | succ a ih =>
    replace ac : a ≈ _ := (exact (succ_pred ⟦a⟧)).symm.trans (pred.spec ac)
    have := ih ac bd
    apply exact
    rw [sound (succ_mul _ _ ), ←mk_add, sound this, sound (pred_mul _ _), ←mk_add,
      sound bd, ←mk_neg, add_assoc, neg_add_cancel, add_zero]
  | pred a ih =>
    replace ac : a ≈ _ := (exact (pred_succ ⟦a⟧)).symm.trans (succ.spec ac)
    have := ih ac bd
    apply exact
    rw [sound (pred_mul _ _), ←mk_add, sound this, sound (succ_mul _ _), ←mk_add,
      ←sound bd, ←mk_neg, add_assoc, add_neg_cancel, add_zero]

instance : Mul BitInt where
  mul := by
    apply Quotient.lift₂ (⟦·.mul ·⟧)
    intro a b c d ac bd
    apply sound
    apply Pre.mul.spec
    assumption
    assumption

@[simp]
def mk_mul (a b: Pre) : ⟦a⟧ * ⟦b⟧ = ⟦a.mul b⟧ := by rfl

@[simp]
def mk_sub (a b: Pre) : ⟦a⟧ - ⟦b⟧ = ⟦a.add b.neg⟧ := by
  show ⟦_⟧ + -⟦_⟧ = _
  simp

instance : IsMulZeroClass BitInt where
  zero_mul a := by
    induction a using ind with | mk a =>
    apply sound
    apply Pre.zero_mul
  mul_zero a := by
    induction a using ind with | mk a =>
    apply sound
    apply Pre.mul_zero

@[simp]
def succ_mul (a b: BitInt) : a.succ * b = a * b + b := by
  induction a, b using ind₂ with | mk a b =>
  apply sound
  apply Pre.succ_mul

@[simp]
def mul_succ (a b: BitInt) : a * b.succ = a * b + a := by
  induction a, b using ind₂ with | mk a b =>
  apply sound
  apply Pre.mul_succ

@[simp]
def pred_mul (a b: BitInt) : a.pred * b = a * b - b := by
  induction a, b using ind₂ with | mk a b =>
  simp
  apply sound
  apply Pre.pred_mul

@[simp]
def mul_pred (a b: BitInt) : a * b.pred = a * b - a := by
  induction a, b using ind₂ with | mk a b =>
  simp
  apply sound
  apply Pre.mul_pred

@[simp]
def negone_mul (a: BitInt) : -1 * a = -a := by
  induction a using ind with | mk a =>
  simp
  apply sound
  apply Pre.negone_mul

@[simp]
def mul_negone (a: BitInt) : a * -1 = -a := by
  induction a using ind with | mk a =>
  simp
  apply sound
  apply Pre.mul_negone

instance : IsMulOneClass BitInt where
  one_mul a := by
    show succ 0 * a = a
    simp
  mul_one a := by
    show a * succ 0 = a
    simp

instance : IsCommMagma BitInt where
  mul_comm a b := by
    induction a, b using ind₂ with | mk a b =>
    apply sound
    apply Pre.mul_comm

instance : IsLeftDistrib BitInt where
  mul_add k a b := by
    induction k with
    | zero => simp
    | succ k ih =>
      simp [ih]
      ac_rfl
    | pred k ih =>
      simp [ih, sub_eq_add_neg,]
      rw [neg_add_rev]
      ac_rfl
instance : IsRightDistrib BitInt := inferInstance

instance : IsSemigroup BitInt where
  mul_assoc a b c := by
    induction a with
    | zero => simp
    | succ a ih => simp [add_mul, ih]
    | pred a ih => simp [sub_mul, ih]

instance : Pow BitInt ℕ where
  pow := flip npowRec

instance : IsMonoid BitInt where

instance : IsRing BitInt := IsRing.inst'

def equivInt : Int ≃+* BitInt where
  toFun n := n
  invFun n := n.toInt
  leftInv := intCast_toInt
  rightInv := toInt_intCast
  map_zero := rfl
  map_one := rfl
  map_add := (intCast_add _ _).symm
  map_mul := (intCast_mul _ _).symm

end BitInt
