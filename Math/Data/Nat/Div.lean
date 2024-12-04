import Math.Data.Nat.Dvd
import Math.Ops.Checked

namespace nat

@[reducible]
noncomputable
def div_rec
  (motive: nat -> ∀b: nat, 0 < b -> Sort _)
  (lt: ∀a b: nat, ∀h: 0 < b, a < b -> motive a b h)
  (ge: ∀a b: nat, ∀h: 0 < b, b ≤ a -> motive (a - b) b h -> motive a b h)
  a b h: motive a b h :=
  if g:a < b then
    lt a b h g
  else
    ge a b h (le_of_not_lt g) (div_rec motive lt ge _ _ h)
termination_by a
decreasing_by
  replace g := le_of_not_lt g
  cases b using cases
  contradiction
  cases a using cases
  contradiction
  rw [succ_sub_succ]
  apply lt_of_le_of_lt
  apply sub_le
  apply lt_succ_self

noncomputable
def div : nat -> ∀den: nat, 0 < den -> nat :=
  div_rec _ (fun _ _ _ _ => 0) (fun _ _ _ _ ih => ih.succ)

noncomputable
def mod : nat -> ∀den: nat, 0 < den -> nat :=
  div_rec _ (fun a _ _ _ => a) (fun _ _ _ _ ih => ih)

def fastDiv (a b: nat) (_h: 0 < b) := ofNat (a.toNat / b.toNat)
def fastMod (a b: nat) (_h: 0 < b) := ofNat (a.toNat % b.toNat)

noncomputable
instance : CheckedDiv nat ((0: nat) < ·) where
  checked_div := div

noncomputable
instance : CheckedMod nat ((0: nat) < ·) where
  checked_mod := mod

def div_rec_of_lt (a b h) (a_lt_b: a < b) : div_rec motive lt ge a b h = lt a b h a_lt_b := by
  unfold div_rec
  rw [dif_pos]
def div_rec_of_ge (a b h) (a_lt_b: b ≤ a) : div_rec motive lt ge a b h = ge a b h a_lt_b (div_rec motive lt ge _ b h) := by
  rw [div_rec, dif_neg]
  apply not_lt_of_le
  assumption

def div_of_lt (a b: nat) (h: 0 < b) : a < b -> a /? b = 0 := by
  show _ -> div _ _ _ = _
  unfold div
  apply div_rec_of_lt
def div_of_ge (a b: nat) (h: 0 < b) : b ≤ a -> a /? b = ((a - b) /? b).succ := by
  show _ -> div _ _ _ = _
  unfold div
  apply div_rec_of_ge

def mod_of_lt (a b: nat) (h: 0 < b) : a < b -> a %? b = a := by
  show _ -> mod _ _ _ = _
  unfold mod
  apply div_rec_of_lt
def mod_of_ge (a b: nat) (h: 0 < b) : b ≤ a -> a %? b = (a - b) %? b := by
  show _ -> mod _ _ _ = _
  unfold mod
  apply div_rec_of_ge

@[csimp]
def div_eq_fastDiv : div = fastDiv := by
  funext a b h
  show a /? b = _
  unfold fastDiv
  induction a, b, h using div_rec with
  | lt a b h a_lt_b =>
    rw [div_of_lt, Nat.div_eq_of_lt]
    rfl
    apply (LT_iff_toNat_lt _ _).mp
    assumption
    assumption
  | ge a b h b_le_a ih =>
    rw [div_of_ge, Nat.div_eq, if_pos]
    show _ = (ofNat (_)).succ
    congr
    rw [lift_sub₂] at ih
    assumption
    apply And.intro
    show toNat 0 < _
    apply (LT_iff_toNat_lt _ _).mp
    assumption
    apply (LE_iff_toNat_le _ _).mp
    assumption
    assumption

@[csimp]
def mod_eq_fastMod : mod = fastMod := by
  funext a b h
  show a %? b = _
  unfold fastMod
  induction a, b, h using div_rec with
  | lt a b h a_lt_b =>
    rw [mod_of_lt, Nat.mod_eq_of_lt]
    rfl
    apply (LT_iff_toNat_lt _ _).mp
    assumption
    assumption
  | ge a b h b_le_a ih =>
    rw [mod_of_ge, Nat.mod_eq, if_pos]
    congr
    rw [lift_sub₂] at ih
    assumption
    apply And.intro
    show toNat 0 < _
    apply (LT_iff_toNat_lt _ _).mp
    assumption
    apply (LE_iff_toNat_le _ _).mp
    assumption
    assumption

instance : CheckedDiv nat ((0: nat) < ·) where
  checked_div := div

instance : CheckedMod nat ((0: nat) < ·) where
  checked_mod := mod

instance : Div nat where
  div a b := if h:0 < b then a /? b else 0
instance : Mod nat where
  mod a b := if h:0 < b then a %? b else a

def udiv_eq_div (a b: nat) (h: 0 < b) : a / b = a /? b := by
  unfold HDiv.hDiv instHDiv Div.div instDiv
  dsimp
  rw [dif_pos]

def umod_eq_mod (a b: nat) (h: 0 < b) : a % b = a %? b := by
  show Mod.mod _ _ = _
  unfold Mod.mod instMod
  dsimp
  rw [dif_pos]

def udiv_zero (a: nat) : a / 0 = 0 := rfl
def umod_zero (a: nat) : a % 0 = a := rfl

def div_add_mod (a b: nat) (bpos: 0 < b) : b * (a /? b) + a %? b = a := by
  induction a, b, bpos using div_rec with
  | lt a b b_pos a_lt_b =>
    rw [div_of_lt, mod_of_lt, mul_zero]
    repeat trivial
  | ge a b b_pos b_le_a ih =>
    rw [div_of_ge, mod_of_ge, mul_succ, add_assoc, ih, add_comm, sub_add_cancel]
    repeat trivial

def udiv_add_umod (a b: nat) : b * (a / b) + a % b = a := by
  cases b using cases with
  | zero => rfl
  | succ b =>
    rw [umod_eq_mod, udiv_eq_div]
    apply div_add_mod
    trivial

def mod_lt (a b: nat) (bpos: 0 < b) : a %? b < b := by
  induction a, b, bpos using div_rec with
  | lt a b b_pos a_lt_b =>
    rw [mod_of_lt]
    repeat assumption
  | ge a b b_pos b_le_a ih =>
    rw [mod_of_ge]
    repeat assumption

def div_spec_le (a b: nat) (bpos: 0 < b) : ∀k, b * k ≤ a -> k ≤ a /? b := by
  intro k bk_le_a
  rw [←div_add_mod a b bpos] at bk_le_a
  apply Decidable.byContradiction
  intro h
  replace h := lt_of_not_le h
  have ⟨k₀, eq⟩  := lt_iff_exists_add_eq.mp h
  subst k
  rw [mul_add] at bk_le_a
  replace bk_le_a := le_add_left_iff_le.mpr bk_le_a
  clear h
  have := lt_of_le_of_lt bk_le_a (mod_lt _ _ _)
  rw [mul_succ] at this
  exact not_le_of_lt this (le_add_right _ _)

def div_spec_ge (a b: nat) (bpos: 0 < b) : ∀k, a ≤ b * k -> a /? b ≤ k := by
  intro k bk_le_a
  rw [←div_add_mod a b bpos] at bk_le_a
  apply Decidable.byContradiction
  intro h
  replace h := lt_of_not_le h
  have ⟨k₀, eq⟩ := lt_iff_exists_add_eq.mp h
  rw [←eq] at bk_le_a
  rw [mul_add, add_assoc] at bk_le_a
  rw [mul_succ, add_assoc b] at bk_le_a
  have ⟨bk_eq_zero, _⟩  := add_eq_zero (eq_zero_of_add_le_self bk_le_a)
  subst b
  contradiction

def div_mul_of_dvd (a b: nat) (bpos: 0 < b) : b ∣ a -> a /? b * b = a := by
  intro ⟨k, h⟩
  have : a /? b = k := by
    apply le_antisymm
    apply div_spec_ge a b bpos k
    rw [h]
    apply div_spec_le a b bpos k
    rw [h]
  subst k
  rw [mul_comm]
  assumption

def mul_div_of_dvd (a b: nat) (bpos: 0 < b) : b ∣ a -> b * (a /? b) = a := by
  intro h
  rw [mul_comm]
  apply div_mul_of_dvd
  assumption

def div_den_congr (a b c: nat) (h: b = c) (bpos: 0 < b) : a /? b = a /? c ~(by
  subst c
  assumption) := by
  subst c
  rfl

def mod_den_congr (a b c: nat) (h: b = c) (bpos: 0 < b) : a %? b = a %? c ~(by
  subst c
  assumption) := by
  subst c
  rfl

def mul_left_div (a b: nat) (bpos: 0 < b) : a * b /? b = a := by
  apply le_antisymm
  apply div_spec_ge
  rw [mul_comm]
  apply div_spec_le
  rw [mul_comm]

def mul_right_div (a b: nat) (bpos: 0 < b) : b * a /? b = a := by
  rw [mul_comm, ]
  apply le_antisymm
  apply div_spec_ge
  rw [mul_comm]
  apply div_spec_le
  rw [mul_comm]

macro_rules | `(tactic|invert_tactic_trivial) => `(tactic|apply add_pos; invert_tactic_trivial)
macro_rules | `(tactic|invert_tactic_trivial) => `(tactic|apply mul_pos <;> invert_tactic_trivial)

def dvd_mod {a b k: nat} (h: 0 < b) : k ∣ a -> k ∣ b -> k ∣ a %? b := by
  intro ka kb
  have := div_add_mod a b h
  rw [←this] at ka
  exact of_dvd_add (by
    apply dvd_trans kb
    apply dvd_mul_right) ka

def mul_div_le (a b: nat) (hb: 0 < b): b * (a /? b) ≤ a := by
  induction a, b, hb using div_rec with
  | lt a b hb ab =>
    rw [div_of_lt, mul_zero]
    apply zero_le
    assumption
  | ge a b hb ba ih  =>
    rw [div_of_ge, mul_succ]
    conv => {
      rhs; rw [←sub_add_cancel _ _ ba, add_comm]
    }
    apply add_le_add
    rfl
    assumption
    assumption

def mul_div_mul (a b k: nat) (hb: 0 < b) (hk: 0 < k) : (a * k) /? (b * k) = a /? b := by
  apply le_antisymm
  · apply div_spec_le
    induction a, b, hb using div_rec with
    | lt a b hb ab =>
      rw [div_of_lt, mul_zero]
      apply zero_le
      apply (lt_mul_right_iff_lt hk).mp
      assumption
    | ge a b hb ba ih  =>
      rw [div_of_ge, mul_succ]
      conv => {
        rhs; rw [←sub_add_cancel _ _ ba, add_comm]
      }
      apply add_le_add
      rfl
      rw [sub_mul] at ih
      assumption
      apply mul_le_mul
      assumption
      rfl
  · apply div_spec_le
    rw [mul_comm b, mul_comm a, mul_assoc]
    apply mul_le_mul
    rfl
    apply mul_div_le

def mod_mul (a b k: nat) (hb: 0 < b) (hk: 0 < k) : (a %? b) * k = (a * k) %? (b * k) := by
  have p1 : (b * (a /? b) + a %? b) * k = a * k := by
    rw [div_add_mod a b (by invert_tactic)]
  replace p1 := p1.trans (div_add_mod (a * k) (b * k) (by invert_tactic)).symm
  rw [add_mul, mul_right_comm, mul_div_mul] at p1
  exact add_left_cancel_iff.mp p1
  assumption

def dvd_iff_mod_eq_zero (a b: nat) (h: 0 < a) : a ∣ b ↔ b %? a = 0 := by
  have := div_add_mod b a h
  apply Iff.intro
  intro dvd
  rw [mul_div_of_dvd b a h dvd] at this
  exact add_eq_left this
  intro h
  exists b /? a
  rw [h, add_zero] at this
  assumption

@[refl]
def dvd_refl (a: nat) : a ∣ a := ⟨1, one_mul _⟩

end nat
