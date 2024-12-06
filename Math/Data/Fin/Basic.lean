import Math.Function.Basic

def Fin.castLE_ne_addNat (x: Fin n) (y: Fin m) : x.castLE (Nat.le_add_left _ _) ≠ y.addNat n := by
  intro h
  cases x with | mk x xLt =>
  cases y with | mk y yLt =>
  unfold Fin.castLE Fin.addNat at h
  dsimp at h
  have := Fin.mk.inj h
  subst x
  exact Nat.not_lt_of_le (Nat.le_add_left _ _) xLt

def Fin.pair (a: Fin n) (b: Fin m) : Fin (n * m) := by
  apply Fin.mk (a * m + b)
  cases n
  exact a.elim0
  rename_i n
  rw [Nat.succ_mul]
  apply Nat.add_lt_add_of_le_of_lt
  apply Nat.mul_le_mul_right
  apply Nat.le_of_lt_succ
  exact a.isLt
  exact b.isLt

def Fin.pair_left (x: Fin (n * m)) : Fin n := by
  apply Fin.mk (x.val / m)
  refine (Nat.div_lt_iff_lt_mul ?_).mpr ?_
  cases m
  rw [Nat.mul_zero] at x
  exact x.elim0
  apply Nat.zero_lt_succ
  exact x.isLt
def Fin.pair_right (x: Fin (n * m)) : Fin m := by
  apply Fin.mk (x.val % m)
  apply Nat.mod_lt
  cases m
  rw [Nat.mul_zero] at x
  exact x.elim0
  apply Nat.zero_lt_succ

def Fin.pair_pair_left (x: Fin n) (y: Fin m) : (pair x y).pair_left = x := by
  unfold pair pair_left
  cases x with | mk x xLt =>
  cases y with | mk y yLt =>
  simp
  refine Nat.div_eq_of_lt_le ?_ ?_
  apply Nat.le_add_right
  rw [Nat.succ_mul]
  apply Nat.add_lt_add_left
  assumption
def Fin.pair_pair_right (x: Fin n) (y: Fin m) : (pair x y).pair_right = y := by
  unfold pair pair_right
  cases y with | mk y yLt =>
  simp
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt]
  assumption

def Fin.pair_split_eq_self (x: Fin (n * m)) : pair x.pair_left x.pair_right = x := by
  cases x with | mk x xLt =>
  unfold pair pair_left pair_right
  dsimp
  congr
  rw [Nat.mul_comm, Nat.div_add_mod]

def Fin.pair.inj : Function.Injective₂ (Fin.pair (n := n) (m := m)) := by
  intro x₀ x₁ y₀ y₁ h
  have h₀: (pair x₀ x₁).pair_left = x₀ := pair_pair_left _ _
  have h₁: (pair x₀ x₁).pair_right = x₁ := pair_pair_right _ _
  rw [h] at h₀ h₁
  rw [pair_pair_left] at h₀
  rw [pair_pair_right] at h₁
  apply And.intro <;> (symm; assumption)

def Fin.sum [Zero α] [Add α] : ∀{n}, (f: Fin n -> α) -> α
| 0, _ => 0
| _ + 1, f => f 0 + Fin.sum (f ∘ Fin.succ)

def Fin.sum_to [Zero α] [Add α] (x: Fin n) (f: Fin n -> α) : α :=
  Fin.sum <| fun y => if y < x then f y else 0

def Fin.sum_zero :
  Fin.sum (fun _: Fin n => 0) = (0: Nat) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold sum
    rw [Nat.zero_add]
    exact ih

def Fin.sum_to_zero (f: Fin (n + 1) -> Nat) :
  Fin.sum_to 0 f = 0 := by
  unfold sum_to
  simp
  rw [sum_zero]

def Fin.sum_succ (f: Fin (n + 1) -> Nat):
  Fin.sum f = f 0 + Fin.sum (f ∘ Fin.succ) := rfl

def Fin.sum_to_succ (f: Fin (n + 1) -> Nat) (x: Fin (n + 1)) (h: x ≠ 0) :
  Fin.sum_to x f = f 0 + Fin.sum_to (x.pred h) (f ∘ Fin.succ) := by
  unfold sum_to
  rw [sum_succ]
  rw[if_pos]
  congr
  · funext x'
    dsimp
    split <;> rename_i g
    rw [if_pos]
    apply Fin.succ_lt_succ_iff.mp
    rw [Fin.succ_pred]
    assumption
    rw [if_neg]
    intro h
    apply g
    apply Fin.pred_lt_pred_iff.mp
    rw [Fin.pred_succ]
    assumption
    exact Fin.succ_ne_zero _
  apply Nat.zero_lt_of_ne_zero
  intro g
  apply h
  exact Fin.val_inj.mp g

def Fin.le_sum (x: Fin n) (f: Fin n -> Nat) : f x ≤ sum f := by
  induction n with
  | zero => exact x.elim0
  | succ n ih =>
    if h:x = 0 then
      subst x
      apply Nat.le_add_right
    else
      apply flip Nat.le_trans
      apply Nat.le_add_left
      apply flip Nat.le_trans
      apply ih (x.pred h)
      dsimp
      rw [Fin.succ_pred]
      apply Nat.le_refl

def Fin.sum_to_lt_sum (x: Fin n) (f: Fin n -> Nat) (y: Fin (f x)) :
  sum_to x f + y.val < sum f := by
  induction n with
  | zero => exact x.elim0
  | succ n ih =>
    if h:x = 0 then
      subst x
      rw [sum_to_zero, Nat.zero_add]
      apply Nat.lt_of_lt_of_le
      apply Fin.isLt
      apply le_sum
    else
      replace ih := ih (x.pred h) (f ∘ Fin.succ)
      simp at ih
      rw [Fin.succ_pred] at ih
      replace ih := ih y
      unfold sum_to at ih
      simp at ih
      rw [Fin.sum_to_succ, sum_succ]
      rw [Nat.add_assoc]
      apply Nat.add_lt_add_left
      apply ih

def Fin.lt_add_sum_to_inj (f: Fin n -> Nat)
    (x₀ x₁: Fin n)
    (y₀: Fin (f x₀))
    (y₁: Fin (f x₁)) :
  y₀.val + sum_to x₀ f = y₁.val + sum_to x₁ f -> x₀ = x₁ ∧ HEq y₀ y₁ := by
  intro eq
  induction n with
  | zero => exact x₀.elim0
  | succ n ih =>
    if h₀:x₀ = 0 then
      subst x₀
      rw [sum_to_zero, Nat.add_zero] at eq
      if h₁:x₁ = 0 then
        subst x₁
        rw [sum_to_zero] at eq
        cases Fin.val_inj.mp eq
        apply And.intro
        rfl
        rfl
      else
        rw [sum_to_succ _ _ h₁]  at eq
        have := y₀.isLt
        rw [eq] at this
        rw [←Nat.add_assoc, Nat.add_comm _ (f 0), Nat.add_assoc] at this
        have := Nat.not_lt_of_le (Nat.le_add_right _ _) this
        contradiction
    else
      rw [sum_to_succ _ _ h₀]  at eq
      if h₁:x₁ = 0 then
        subst x₁
        rw [sum_to_zero] at eq
        replace eq : _ = y₁.val := eq
        have := y₁.isLt
        rw [←eq] at this
        rw [←Nat.add_assoc, Nat.add_comm _ (f 0), Nat.add_assoc] at this
        have := Nat.not_lt_of_le (Nat.le_add_right _ _) this
        contradiction
      else
        rw [sum_to_succ _ _ h₁]  at eq
        rw [Nat.add_left_comm y₀, Nat.add_left_comm y₁] at eq
        replace eq := Nat.add_left_cancel eq
        replace ih := ih (f ∘ Fin.succ) (x₀.pred h₀) (x₁.pred h₁) (by
          apply Fin.mk y₀.val
          simp) (by
          apply Fin.mk y₁.val
          simp) eq
        simp at ih
        obtain ⟨a, b⟩ := ih
        cases a
        cases y₀; cases y₁
        cases b
        apply And.intro <;> rfl
