import Math.Function.Basic
import Math.Type.Basic
import Math.Algebra.Order
import Math.Algebra.Impls.Nat
import Math.Data.Fin.Pairing

def Fin.castLE_ne_addNat (x: Fin n) (y: Fin m) : x.castLE (Nat.le_add_left _ _) ≠ y.addNat n := by
  intro h
  cases x with | mk x xLt =>
  cases y with | mk y yLt =>
  unfold Fin.castLE Fin.addNat at h
  dsimp at h
  have := Fin.mk.inj h
  subst x
  exact Nat.not_lt_of_le (Nat.le_add_left _ _) xLt

variable [Zero α] [Add α]

def Fin.sum : ∀{n}, (f: Fin n -> α) -> α
| 0, _ => 0
| _ + 1, f => f 0 + Fin.sum (f ∘ Fin.succ)

def Fin.sum' : ∀{n}, (f: Fin n -> α) -> α
| 0, _ => 0
| _ + 1, f => f (Fin.last _) + Fin.sum' (f ∘ (Fin.castLE (Nat.le_succ _)))
def Fin.sum_to (x: Fin n) (f: Fin n -> α) : α :=
  Fin.sum <| fun y => if y < x then f y else 0

variable [IsAddZeroClass α] [IsAddSemigroup α]

def Fin.sum_zero :
  Fin.sum (fun _: Fin n => 0) = (0: α) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold sum
    rw [zero_add]
    exact ih

def Fin.sum_to_zero (f: Fin (n + 1) -> α) :
  Fin.sum_to 0 f = 0 := by
  unfold sum_to
  simp
  rw [sum_zero]

def Fin.sum_succ (f: Fin (n + 1) -> α):
  Fin.sum f = f 0 + Fin.sum (f ∘ Fin.succ) := rfl

def Fin.sum_to_succ (f: Fin (n + 1) -> α) (x: Fin (n + 1)) (h: x ≠ 0) :
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

variable [LE α] [LT α] [SMul ℕ α] [IsOrderedAddCommMonoid α]

def Fin.zero_le_sum (f: Fin n -> α) (f_nonneg: ∀x, 0 ≤ f x) : 0 ≤ sum f := by
  induction n with
  | zero =>
    unfold sum
    rfl
  | succ n ih =>
    unfold sum
    rw [←add_zero 0]
    apply add_le_add
    apply f_nonneg
    apply ih
    intro
    apply f_nonneg

def Fin.le_sum (x: Fin n) (f: Fin n -> α) (f_nonneg: ∀x, 0 ≤ f x := by intro; apply Nat.zero_le _) : f x ≤ sum f := by
  replace f_nonneg: ∀x, 0 ≤ f x := f_nonneg
  induction n with
  | zero => exact x.elim0
  | succ n ih =>
    if h:x = 0 then
      subst x
      rw [←add_zero (f 0), sum_succ]
      apply add_le_add_left
      apply zero_le_sum
      intro x
      apply f_nonneg
    else
      apply flip le_trans
      apply add_le_add_left
      apply flip le_trans
      apply ih (x.pred h)
      dsimp
      intro
      apply f_nonneg
      rfl
      simp
      conv => {
        lhs
        rw [←zero_add (f x)]
      }
      apply add_le_add_right
      apply f_nonneg

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
      intro
      apply Nat.zero_le
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

def Fin.powTwoSum (f : Fin n -> Bool) := Fin.sum' (fun x => if f x then 2 ^ x.val else 0)

def Fin.powTwoSum_lt {f: Fin n -> Bool} : powTwoSum f < 2 ^ n := by
  induction n with
  | zero => apply Nat.zero_lt_succ
  | succ n ih =>
    rw [Nat.pow_succ, Nat.mul_two]
    apply Nat.add_lt_add_of_le_of_lt
    simp
    split
    rfl
    apply Nat.zero_le
    apply Nat.lt_of_le_of_lt _ (ih (f := fun x => f <| x.castLE (Nat.le_succ _)))
    unfold powTwoSum
    apply Nat.le_of_eq
    congr

def Fin.powTwoSum_inj : Function.Injective (Fin.powTwoSum (n := n)) := by
  intro x y eq
  funext i
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    have eq : (if _ then _ else _) + powTwoSum _ = (if _ then _ else _) + powTwoSum _ := eq
    split at eq <;> split at eq
    all_goals
      rename_i hx hy
      simp at eq
      generalize ihx_def:(powTwoSum fun x_1 => x (castLE (Nat.le_succ _) x_1)) = ihx
      generalize ihy_def:(powTwoSum fun x_1 => y (castLE (Nat.le_succ _) x_1)) = ihy
      have ihx_lt: ihx < 2 ^ n := by
        subst ihx
        exact powTwoSum_lt
      have ihy_lt: ihy < 2 ^ n := by
        subst ihy
        exact powTwoSum_lt
    · if h:i = Fin.last _ then
        subst i
        rw [hx, hy]
      else
        have := ih eq ⟨i.val, lt_of_le_of_ne (Nat.le_of_lt_succ i.isLt) (by
          intro g
          apply h
          apply Fin.val_inj.mp g)⟩
        unfold castLE at this
        exact this
    · rw [ihx_def, ihy_def] at eq
      rw [←eq] at ihy_lt
      have := Nat.not_lt_of_le (Nat.le_add_right _ _) ihy_lt
      contradiction
    · rw [ihx_def, ihy_def] at eq
      rw [eq] at ihx_lt
      have := Nat.not_lt_of_le (Nat.le_add_right _ _) ihx_lt
      contradiction
    · if h:i = Fin.last _ then
        subst i
        rw [Bool.eq_false_iff.mpr hx, Bool.eq_false_iff.mpr hy]
      else
        have := ih eq ⟨i.val, lt_of_le_of_ne (Nat.le_of_lt_succ i.isLt) (by
          intro g
          apply h
          apply Fin.val_inj.mp g)⟩
        unfold castLE at this
        exact this

def Fin.isoPair : Fin n × Fin m ≃ Fin (n * m) where
  toFun x := Fin.pair x.1 x.2
  invFun x := ⟨x.pair_left, x.pair_right⟩
  leftInv := by
    intro x
    simp
    rw [pair_pair_left, pair_pair_right]
  rightInv := by
    intro x
    simp
    rw [pair_split_eq_self]

def Fin.equivAdd (n m: Nat) : Fin n ⊕ Fin m ≃ Fin (n + m) where
  toFun
  | .inl x => x.addNat m
  | .inr x => x.castLE (Nat.le_add_left _ _)
  invFun x :=
    if h:x.val < m then .inr ⟨x, h⟩ else .inl ⟨x.val - m, by
      apply Nat.sub_lt_left_of_lt_add
      apply Nat.le_of_not_lt
      assumption
      cases x; dsimp
      rw [Nat.add_comm]; assumption⟩
  leftInv x := by
    dsimp
    cases x <;> rename_i x <;> dsimp
    rw [dif_neg]
    congr
    rw [Nat.add_sub_cancel]
    apply Nat.not_lt_of_le
    apply Nat.le_add_left
    rw [dif_pos]
    exact x.isLt
  rightInv x := by
    dsimp
    by_cases h:x.val < m
    rw [dif_pos h]
    rfl
    rw [dif_neg h]
    dsimp; congr
    rw [Nat.sub_add_cancel]
    apply Nat.le_of_not_lt
    assumption

def Fin.equivMul (n m: Nat) : Fin n × Fin m ≃ Fin (n * m) where
  toFun | ⟨x, y⟩ => Fin.pair x y
  invFun x := ⟨x.pair_left, x.pair_right⟩
  leftInv x := by
    dsimp
    rw [Fin.pair_pair_left]
    rw [Fin.pair_pair_right]
  rightInv x := by
    dsimp
    rw [Fin.pair_split_eq_self]

def Fin.addNat_inj : Function.Injective (Fin.addNat · k (n := n)) := by
  intro ⟨x, _⟩ ⟨y, _⟩ eq
  replace eq := Fin.val_inj.mpr eq
  dsimp at eq
  congr
  exact Nat.add_right_cancel eq

def Fin.sum_eq_zero_of_each_eq_zero
  [Add α] [Zero α] [IsAddZeroClass α]
  (f: Fin n -> α)
  (h: ∀x, f x = 0) : Fin.sum f = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold sum
    rw [ih, add_zero, h]
    intro x
    apply h

def Fin.sum_succ' [Add α] [Zero α] [IsAddZeroClass α] [IsAddSemigroup α]
  (f: Fin (n + 1) -> α):
  Fin.sum f = Fin.sum (f ∘ Fin.castSucc) + f (Fin.last _) := by
    induction n with
    | zero =>
      rw [sum_succ, sum, add_zero, sum]
      symm; apply zero_add
    | succ n ih =>
      rw [sum, ih, ←add_assoc]
      rfl

def Fin.sum_eq_sum_of_prefix
  [Add α] [Zero α] [IsAddZeroClass α]
  (f: Fin n -> α)
  (g: Fin m -> α)
  (h₀: ∀x: Fin (min n m), f (x.castLE (Nat.min_le_left _ _)) = g (x.castLE (Nat.min_le_right _ _)))
  (h₁: ∀x: Fin n, m ≤ x.val -> f x = 0)
  (h₂: ∀x: Fin m, n ≤ x.val -> g x = 0): Fin.sum f = Fin.sum g := by
  induction n generalizing m with
  | zero =>
    rw [sum, sum_eq_zero_of_each_eq_zero]
    intro x
    rw [h₂]
    apply Nat.zero_le
  | succ n ih =>
    cases m with
    | zero =>
      symm; rw [sum, sum_eq_zero_of_each_eq_zero]
      intro
      rw [h₁]
      apply Nat.zero_le
    | succ m =>
      rw [sum, sum]
      congr 1
      apply h₀ ⟨0, _⟩
      apply Nat.lt_min.mpr
      apply And.intro <;> apply Nat.zero_lt_succ
      apply ih
      · intro x
        apply h₀ ⟨x.val+1, _⟩
        rw [Nat.add_min_add_right]
        apply Nat.add_lt_add_right
        apply Fin.isLt
      · intro x h
        dsimp
        rw [h₁]
        apply Nat.succ_le_succ
        assumption
      · intro x h
        dsimp
        rw [h₂]
        apply Nat.succ_le_succ
        assumption

def Fin.sum_strip_prefix
  [IsAddLeftCancel α]
  {f: Fin n -> α} {g: Fin m -> α} (k: Nat) (hkn: k ≤ n) (hkm: k ≤ m) :
  (∀x: Fin k, f (x.castLE hkn) = g (x.castLE hkm)) ->
  Fin.sum f = Fin.sum g ->
  Fin.sum (fun x: Fin (n - k) => f <| (x.addNat k).cast (Nat.sub_add_cancel hkn)) = Fin.sum (fun x: Fin (m - k) => g <| (x.addNat k).cast (Nat.sub_add_cancel hkm)) := by
  induction k generalizing n m with
  | zero =>
    intro pre
    exact id
  | succ k ih =>
    intro pre eq
    cases n with
    | zero => contradiction
    | succ n =>
    cases m with
    | zero => contradiction
    | succ m =>
      erw [sum, sum, pre ⟨0, Nat.zero_lt_succ _⟩] at eq
      replace eq: g 0 + _ = g 0 + _ := eq
      replace eq := add_left_cancel eq
      replace ih := ih (n := n) (m := m) (f := f ∘ succ) (g := g ∘ succ) (Nat.le_of_succ_le_succ hkn) (Nat.le_of_succ_le_succ hkm)
        ?_ eq
      unfold Fin.cast
      dsimp
      unfold succ addNat Fin.cast at ih
      dsimp at ih
      suffices
        (sum fun x: Fin ((n+1) - (k+1)) => f ⟨↑x + (k + 1), _⟩) = (sum fun x: Fin (n - k) => f ⟨↑x + k + 1, _⟩) ∧
        (sum fun x: Fin ((m+1) - (k+1)) => g ⟨↑x + (k + 1), _⟩) = (sum fun x: Fin (m - k) => g ⟨↑x + k + 1, _⟩)
        by
        rw [this.left, this.right]
        exact ih
      apply And.intro
      any_goals
        apply Fin.sum_eq_sum_of_prefix
        intro
        unfold castLE
        dsimp
        rfl
        all_goals
          intro x h
          have := Nat.lt_of_le_of_lt h x.isLt
          rw [Nat.succ_sub_succ] at this
          have := Nat.lt_irrefl _ this
          contradiction
      intro x
      apply pre ⟨_, _⟩
      apply Nat.succ_lt_succ
      exact x.isLt

def Fin.sum_extend [Add α] [Zero α] [IsAddZeroClass α] (f: Fin n -> α) (h: n ≤ m) :
  Fin.sum f = Fin.sum fun x: Fin m => if h:x.val < n then f ⟨_, h⟩ else 0 := by
  induction m generalizing n with
  | zero =>
    cases Nat.le_zero.mp h
    rfl
  | succ m ih =>
    cases n with
    | zero =>
      rw [sum, sum_eq_zero_of_each_eq_zero]
      intro x
      rw [dif_neg]
      exact Nat.not_lt_zero ↑x
    | succ n =>
      rw [sum, sum, dif_pos, ih]
      congr
      ext i
      simp
      omega

def Fin.sum_mul [Add α] [Zero α] [Mul α] [IsMulZeroClass α] [IsRightDistrib α] (f: Fin n -> α) (x: α) :
  Fin.sum f * x = Fin.sum (fun i => f i * x) := by
  induction n with
  | zero => rw [sum, sum, zero_mul]
  | succ n ih =>
    rw [sum_succ, sum_succ, add_mul, ih]
    rfl

def Fin.sum_pop [Zero α] [Add α] [IsAddZeroClass α] [IsAddSemigroup α]
  (f: Fin (n + 1) -> α) : Fin.sum f = Fin.sum (fun x: Fin n => f x.castSucc) + f (Fin.last _) := by
  induction n with
  | zero => simp [sum]
  | succ n ih =>
    rw [sum, ih, sum, ←add_assoc]
    rfl

def Fin.sum_rev [Zero α] [Add α] [IsAddZeroClass α] [IsAddSemigroup α] [IsAddCommMagma α]
  (f: Fin n -> α) : Fin.sum f = Fin.sum (f ∘ Fin.rev) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sum, sum_pop, add_comm, ih]
    congr
    · ext x
      dsimp
      unfold rev succ castSucc castAdd castLE
      dsimp
      congr
      rw [Nat.succ_sub]
      apply Nat.le_of_lt_succ
      apply Nat.succ_lt_succ
      exact x.isLt
    rw [Fin.rev_last]

def Fin.sum_add_sum [Zero α] [Add α] [IsAddZeroClass α] [IsAddSemigroup α] [IsAddCommMagma α]
  (f g: Fin n -> α) : Fin.sum f + Fin.sum g = Fin.sum (fun n => f n + g n) := by
  induction n with
  | zero =>
    erw [add_zero]
    rfl
  | succ n ih =>
    simp [sum]
    rw [
      ←add_assoc, add_comm _ (g 0),
      ←add_assoc, add_comm (g 0),
      add_assoc, ih (f ∘ succ) (g ∘ succ)]
    rfl
