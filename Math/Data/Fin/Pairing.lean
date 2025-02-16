import Math.Function.Basic

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
  rw [Nat.mod_eq_of_lt]
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

def Fin.pair.congr (a b: Fin (n * m)) : pair_left a = pair_left b -> pair_right a = pair_right b -> a = b := by
  intro x y
  rw [←pair_split_eq_self a, x, y, pair_split_eq_self]
