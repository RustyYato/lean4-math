import Math.Type.Notation
import Math.Order.OrderIso
import Math.Order.TopBot

inductive ENat where
| ofNat (n: ℕ)
| inf

notation "ℕ∞" => ENat

namespace ENat

attribute [coe] ENat.ofNat

scoped notation "∞" => ENat.inf

instance : NatCast ENat := ⟨ENat.ofNat⟩
instance : OfNat ENat n := ⟨n⟩

protected inductive LE : ENat -> ENat -> Prop where
| le_inf (x: ENat) : ENat.LE x ∞
| ofNat (x y: ℕ) : x ≤ y -> ENat.LE x y

protected inductive LT : ENat -> ENat -> Prop where
| lt_inf (x: ℕ) : ENat.LT x ∞
| ofNat (x y: ℕ) : x < y -> ENat.LT x y

instance : LE ENat := ⟨ENat.LE⟩
instance : LT ENat := ⟨ENat.LT⟩

@[simp] def le_inf (x: ENat) : x ≤ ∞ := ENat.LE.le_inf _
@[simp] def natCast_le_natCast (x y: ℕ) : (x: ℕ∞) ≤ y ↔ x ≤ y := by
  apply Iff.intro
  intro h
  cases h
  assumption
  intro h
  apply ENat.LE.ofNat
  assumption

@[simp] def natCast_lt_inf (x: ℕ) : x < ∞ := ENat.LT.lt_inf _
@[simp] def natCast_lt_natCast (x y: ℕ) : (x: ℕ∞) < y ↔ x < y := by
  apply Iff.intro
  intro h
  cases h
  assumption
  apply ENat.LT.ofNat

def oeqv : ℕ∞ ≃o WithTop ℕ where
  toFun
  | ∞ => ⊤
  | (x: ℕ) => x
  invFun
  | ⊤ => ∞
  | (x: ℕ) => x
  leftInv x := by cases x <;> rfl
  rightInv x := by cases x <;> rfl
  map_le a b := by
    cases a <;> cases b
    simp; apply natCast_le_natCast
    simp [le_top]
    simp
    nofun
    simp

instance : IsLawfulLT ℕ∞ where
  lt_iff_le_and_not_le := by
    intro a b
    apply Iff.intro
    · intro h; cases h
      simp
      nofun
      rename_i h
      simp [h]
      apply le_of_lt h
    · intro ⟨h, g⟩
      cases h
      cases a
      apply natCast_lt_inf
      exfalso
      exact g (le_inf _)
      simpa using g
instance : IsLinearOrder ℕ∞ := oeqv.instIsLinearOrder

def inf_not_lt (x: ℕ∞) : ¬∞ < x := by simp [←not_le]

def max : ℕ∞ -> ℕ∞ -> ℕ∞
| ∞, _ | _, ∞ => ∞
| (n: ℕ), (m: ℕ) => (n ⊔ m: ℕ)

def min : ℕ∞ -> ℕ∞ -> ℕ∞
| ∞, x | x, ∞ => x
| (n: ℕ), (m: ℕ) => (n ⊓ m: ℕ)

instance : Max ℕ∞ := ⟨max⟩
instance : Min ℕ∞ := ⟨min⟩

def leqv : ℕ∞ ≃⊓⊔ WithTop ℕ := {
  oeqv with
  map_max a b := by cases a <;> cases b <;> rfl
  map_min a b := by cases a <;> cases b <;> rfl
}

instance : IsDecidableLinearOrder ℕ∞ :=
  leqv.instIsDecidableLinearOrder (by
    intro a b; simp [map_min]) (by
    intro a b; simp [map_max])

instance : Top ℕ∞ where
  top := ∞
instance : Bot ℕ∞ where
  bot := 0

instance : IsLawfulTop ℕ∞ where
  le_top := le_inf
instance : IsLawfulBot ℕ∞ where
  bot_le a := by
    cases a
    apply (natCast_le_natCast _ _).mpr
    apply bot_le
    apply le_inf

instance : @Relation.IsWellFounded ℕ∞ (· < ·) where
  wf := by
    suffices ∀n: ℕ, @Acc ℕ∞ (· < ·) n by
      apply WellFounded.intro
      intro a
      cases a
      apply this
      apply Acc.intro
      intro y h
      cases h
      apply this
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
    apply Acc.intro
    intro m h
    cases h
    apply ih
    assumption

instance : WellFoundedRelation ℕ∞ where
  rel a b := a < b
  wf := Relation.wellFounded _

instance : DecidableEq ℕ∞ := oeqv.toEmbedding.DecidableEq

def add : ℕ∞ -> ℕ∞ -> ℕ∞
| ∞, _ | _, ∞ => ∞
| (n: ℕ), (m: ℕ) => (n + m: ℕ)

instance : Add ℕ∞ := ⟨add⟩

def mul : ℕ∞ -> ℕ∞ -> ℕ∞
| 0, _ | _, 0 => 0
| ∞, _ | _, ∞ => ∞
| (n: ℕ), (m: ℕ) => (n * m: ℕ)

instance : Mul ℕ∞ := ⟨mul⟩

def pow : ℕ∞ -> ℕ∞ -> ℕ∞
| _, 0 | 1, _ => 1
| 0, _ => 0
| ∞, _ | _, ∞ => ∞
| (n: ℕ), (m: ℕ) => (n ^ m: ℕ)

instance : Pow ℕ∞ ℕ∞ := ⟨pow⟩

def natCast_eq_ofNat (a: ℕ) : (a: ℕ∞) = .ofNat a := rfl

@[simp] def inf_add (a: ℕ∞) : ∞ + a = ∞ := by cases a <;> rfl
@[simp] def add_inf (a: ℕ∞) : a + ∞ = ∞ := by cases a <;> rfl
@[simp] def natCast_add_natCast (a b: ℕ) : (a + b: ℕ∞) = (a + b: ℕ) := rfl

@[simp] def natCast_zero : (0: ℕ) = (0: ℕ∞) := rfl
@[simp] def natCast_one : (1: ℕ) = (1: ℕ∞) := rfl

@[simp] def ofNat_zero : (.ofNat 0) = (0: ℕ∞) := rfl
@[simp] def ofNat_one : (.ofNat 1) = (1: ℕ∞) := rfl

@[simp] def zero_mul (a: ℕ∞) : 0 * a = 0 := by
  match a with
  | 0 => rfl
  | (n + 1: ℕ) => rfl
  | ∞ => rfl
@[simp] def mul_zero (a: ℕ∞) : a * 0 = 0 := by
  match a with
  | 0 => rfl
  | (n + 1: ℕ) => rfl
  | ∞ => rfl

@[simp] def inf_mul (a: ℕ∞) (ha: a ≠ 0) : ∞ * a = ∞ :=
  match a with
  | (_ + 1: ℕ) => rfl
  | ∞ => rfl
@[simp] def mul_inf (a: ℕ∞) (ha: a ≠ 0) : a * ∞ = ∞ :=
  match a with
  | (_ + 1: ℕ) => rfl
  | ∞ => rfl
@[simp] def natCast_mul_natCast (a b: ℕ) : (a * b: ℕ∞) = (a * b: ℕ) :=
  match a, b with
  | 0, 0 => rfl
  | 0, n + 1 => by simp
  | n + 1, 0 => rfl
  | n + 1, m + 1 => rfl

def pow_cases
  {motive: ℕ∞ -> ℕ∞ -> Sort*}
  (zero_right: ∀a, motive a 0)
  (one_left: ∀n, n ≠ 0 -> motive 1 n)
  (zero_left: ∀n, n ≠ 0 -> motive 0 n)
  (inf_left: ∀n, n ≠ 0 -> motive ∞ n)
  (inf_right: ∀n: ℕ, 1 < n -> motive n ∞)
  (natCast: ∀n m, 1 < n -> m ≠ 0 -> motive n m)
  (a b: ℕ∞) : motive a b :=
  match a, b with
  | _, 0 => zero_right _
  | 0, (n + 1: ℕ) => zero_left _ nofun
  | 0, ∞ => zero_left _ nofun
  | 1, (_ + 1: ℕ) => one_left _ nofun
  | 1, ∞ => one_left _ nofun
  | ∞, (_ + 1: ℕ) => inf_left _ nofun
  | ∞, ∞ => inf_left _ nofun
  | (_ + 2: ℕ), ∞ => inf_right _ (by simp)
  | (_ + 2: ℕ), (_ + 1: ℕ) => natCast _ _ (by
    apply (natCast_lt_natCast _ _).mpr
    simp) nofun

def pow_def (a b: ℕ∞) : a ^ b = pow a b := rfl

@[simp] def pow_zero (a: ℕ∞) : a ^ (0: ℕ∞) = 1 := by
  rw [pow_def]
  unfold pow
  split
  any_goals trivial
  rename_i h
  cases h
  simp

@[simp] def one_pow (a: ℕ∞) : (1: ℕ∞) ^ a = 1 := by
  rw [pow_def]
  unfold pow
  split
  any_goals trivial
  rename_i h
  cases h
  simp

@[simp] def zero_pow (a: ℕ∞) (ha: a ≠ 0) : (0: ℕ∞) ^ a = 0 := by
  rw [pow_def]
  unfold pow
  split
  any_goals trivial
  rename_i h
  cases h
  simp
  rename_i m _ _ _
  cases m
  contradiction
  rfl

@[simp] def inf_pow (a: ℕ∞) (ha: a ≠ 0) : ∞ ^ a = ∞ := by
  rw [pow_def]
  unfold pow
  split
  any_goals trivial

@[simp] def pow_inf (a: ℕ∞) (ha: 1 < a) : a ^ ∞ = ∞ := by
  rw [pow_def]
  unfold pow
  split
  any_goals trivial

@[simp] def natCast_pow_natCast (a b: ℕ) (ha: 1 < a) (hb: b ≠ 0) : (a: ℕ∞) ^ (b: ℕ∞) = (a ^ b: ℕ) := by
  rw [pow_def]
  unfold pow
  split
  any_goals trivial
  rename_i h; cases h
  contradiction
  rename_i h _
  cases h
  simp
  rename_i h _
  cases h
  cases b
  contradiction
  simp
  rename_i h g
  cases h; cases g
  rfl

def toNat : ℕ∞ -> ℕ
| ∞ => 0
| (n: ℕ) => n

end ENat
