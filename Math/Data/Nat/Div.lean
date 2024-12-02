import Math.Data.Nat.Dvd
import Math.CheckedOps.Basic

noncomputable
def nat.div_rec
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
  cases b using nat.cases
  contradiction
  cases a using nat.cases
  contradiction
  rw [succ_sub_succ]
  apply lt_of_le_of_lt
  apply sub_le
  apply lt_succ_self

noncomputable
def nat.div : nat -> ∀den: nat, 0 < den -> nat :=
  nat.div_rec _ (fun _ _ _ _ => 0) (fun _ _ _ _ ih => ih.succ)

noncomputable
def nat.mod : nat -> ∀den: nat, 0 < den -> nat :=
  nat.div_rec _ (fun a _ _ _ => a) (fun _ _ _ _ ih => ih)

def nat.fastDiv (a b: nat) (_h: 0 < b) := nat.ofNat (a.toNat / b.toNat)
def nat.fastMod (a b: nat) (_h: 0 < b) := nat.ofNat (a.toNat % b.toNat)

noncomputable
instance : CheckedDiv nat ((0: nat) < ·) where
  checked_div := nat.div

noncomputable
instance : CheckedMod nat ((0: nat) < ·) where
  checked_mod := nat.mod

def nat.div_rec_of_lt (a b h) (a_lt_b: a < b) : nat.div_rec motive lt ge a b h = lt a b h a_lt_b := by
  unfold div_rec
  rw [dif_pos]
def nat.div_rec_of_ge (a b h) (a_lt_b: b ≤ a) : nat.div_rec motive lt ge a b h = ge a b h a_lt_b (nat.div_rec motive lt ge _ b h) := by
  rw [div_rec, dif_neg]
  apply not_lt_of_le
  assumption

def nat.div_of_lt (a b: nat) (h: 0 < b) : a < b -> a /? b = 0 := div_rec_of_lt a b h
def nat.div_of_ge (a b: nat) (h: 0 < b) : b ≤ a -> a /? b = ((a - b) /? b).succ := div_rec_of_ge a b h

def nat.mod_of_lt (a b: nat) (h: 0 < b) : a < b -> a %? b = a := div_rec_of_lt a b h
def nat.mod_of_ge (a b: nat) (h: 0 < b) : b ≤ a -> a %? b = (a - b) %? b := div_rec_of_ge a b h

@[csimp]
def nat.div_eq_fastDiv : nat.div = nat.fastDiv := by
  funext a b h
  show a /? b = _
  unfold fastDiv
  induction a, b, h using div_rec with
  | lt a b h a_lt_b =>
    rw [div_of_lt, Nat.div_eq_of_lt]
    rfl
    apply (nat.LT_iff_toNat_lt _ _).mp
    assumption
    assumption
  | ge a b h b_le_a ih =>
    rw [div_of_ge, Nat.div_eq, if_pos]
    show _ = (nat.ofNat (_)).succ
    congr
    rw [lift_sub₂] at ih
    assumption
    apply And.intro
    show nat.toNat 0 < _
    apply (nat.LT_iff_toNat_lt _ _).mp
    assumption
    apply (nat.LE_iff_toNat_le _ _).mp
    assumption
    assumption

@[csimp]
def nat.mod_eq_fastMod : nat.mod = nat.fastMod := by
  funext a b h
  show a %? b = _
  unfold fastMod
  induction a, b, h using div_rec with
  | lt a b h a_lt_b =>
    rw [mod_of_lt, Nat.mod_eq_of_lt]
    rfl
    apply (nat.LT_iff_toNat_lt _ _).mp
    assumption
    assumption
  | ge a b h b_le_a ih =>
    rw [mod_of_ge, Nat.mod_eq, if_pos]
    congr
    rw [lift_sub₂] at ih
    assumption
    apply And.intro
    show nat.toNat 0 < _
    apply (nat.LT_iff_toNat_lt _ _).mp
    assumption
    apply (nat.LE_iff_toNat_le _ _).mp
    assumption
    assumption

instance : CheckedDiv nat ((0: nat) < ·) where
  checked_div := nat.div

instance : CheckedMod nat ((0: nat) < ·) where
  checked_mod := nat.mod

instance : Div nat where
  div a b := if h:0 < b then a /? b else 0
instance : Mod nat where
  mod a b := if h:0 < b then a %? b else a

def nat.udiv_eq_div (a b: nat) (h: 0 < b) : a / b = a /? b := by
  unfold HDiv.hDiv instHDiv Div.div instDivNat
  dsimp
  rw [dif_pos]

def nat.umod_eq_mod (a b: nat) (h: 0 < b) : a % b = a %? b := by
  show Mod.mod _ _ = _
  unfold Mod.mod instModNat
  dsimp
  rw [dif_pos]

def nat.udiv_zero (a: nat) : a / 0 = 0 := rfl
def nat.umod_zero (a: nat) : a % 0 = a := rfl

def nat.div_add_mod (a b: nat) (bpos: 0 < b) : b * (a /? b) + a %? b = a := by
  induction a, b, bpos using div_rec with
  | lt a b b_pos a_lt_b =>
    rw [div_of_lt, mod_of_lt, mul_zero]
    repeat trivial
  | ge a b b_pos b_le_a ih =>
    rw [div_of_ge, mod_of_ge, mul_succ, add_assoc, ih, add_comm, sub_add_cancel]
    repeat trivial

def nat.udiv_add_umod (a b: nat) : b * (a / b) + a % b = a := by
  cases b using cases with
  | zero => rfl
  | succ b =>
    rw [umod_eq_mod, udiv_eq_div]
    apply div_add_mod
    trivial

def nat.mod_lt (a b: nat) (bpos: 0 < b) : a %? b < b := by
  induction a, b, bpos using div_rec with
  | lt a b b_pos a_lt_b =>
    rw [mod_of_lt]
    repeat assumption
  | ge a b b_pos b_le_a ih =>
    rw [mod_of_ge]
    repeat assumption

def nat.div_spec_le (a b: nat) (bpos: 0 < b) : ∀k, b * k ≤ a -> k ≤ a /? b := by
  intro k bk_le_a
  rw [←div_add_mod a b bpos] at bk_le_a
  apply Decidable.byContradiction
  intro h
  replace h := lt_of_not_le h
  have ⟨k₀, eq⟩  := lt_iff_exists_add_eq.mp h
  subst k
  rw [mul_add] at bk_le_a
  replace bk_le_a := nat.le_add_left_iff_le.mpr bk_le_a
  clear h
  have := lt_of_le_of_lt bk_le_a (mod_lt _ _ _)
  rw [mul_succ] at this
  exact not_le_of_lt this (nat.le_add_right _ _)

def nat.div_spec_ge (a b: nat) (bpos: 0 < b) : ∀k, a ≤ b * k -> a /? b ≤ k := by
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

def nat.div_mul_of_dvd (a b: nat) (bpos: 0 < b) : b ∣ a -> a /? b * b = a := by
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

def nat.mul_div_of_dvd (a b: nat) (bpos: 0 < b) : b ∣ a -> b * (a /? b) = a := by
  intro h
  rw [mul_comm]
  apply div_mul_of_dvd
  assumption

def nat.mul_div (a b: nat) (bpos: 0 < b) : a * b /? b = a := by
  apply le_antisymm
  apply div_spec_ge
  rw [mul_comm]
  apply div_spec_le
  rw [mul_comm]
