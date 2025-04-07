import Math.Function.Basic
import Math.Logic.Equiv.Defs

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

@[simp]
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
@[simp]
def Fin.pair_pair_right (x: Fin n) (y: Fin m) : (pair x y).pair_right = y := by
  unfold pair pair_right
  cases y with | mk y yLt =>
  simp
  rw [Nat.mod_eq_of_lt]
  assumption

@[simp]
def Fin.pair_split_eq_self (x: Fin (n * m)) : pair x.pair_left x.pair_right = x := by
  cases x with | mk x xLt =>
  unfold pair pair_left pair_right
  dsimp
  congr
  rw [Nat.mul_comm, Nat.div_add_mod]

def Equiv.finProd : Fin n × Fin m ≃ Fin (n * m) where
  toFun x := x.1.pair x.2
  invFun x := ⟨x.pair_left, x.pair_right⟩
  leftInv x := by simp
  rightInv x := by simp

@[simp] def Equiv.symm_finProd_fst (x: Fin (n * m)) : (Equiv.finProd.symm x).1 = x.pair_left := _root_.rfl
@[simp] def Equiv.symm_finProd_snd (x: Fin (n * m)) : (Equiv.finProd.symm x).2 = x.pair_right := _root_.rfl

def Fin.pair.inj : Function.Injective₂ (Fin.pair (n := n) (m := m)) := by
  intro a b c d h
  replace h : Equiv.finProd ⟨a, b⟩ = Equiv.finProd ⟨c, d⟩ := h
  exact Prod.mk.inj (Equiv.finProd.inj h)

def Fin.pair.congr (a b: Fin (n * m)) : pair_left a = pair_left b -> pair_right a = pair_right b -> a = b := by
  intro x y
  apply Equiv.finProd.symm.inj
  ext; simp [x]; simp [y]
