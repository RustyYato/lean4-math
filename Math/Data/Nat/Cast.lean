namespace Nat

class AtLeastTwo (n: Nat) where
  prop: 2 ≤ n

instance instAtLeastTwo : AtLeastTwo (n + 2) where
  prop := Nat.le_add_left _ _

instance instOfNatOfNatCast [NatCast α] [AtLeastTwo n] : OfNat α n where
  ofNat := n

end Nat

variable (n : Nat) [n.AtLeastTwo]

def two_le : 2 ≤ n := Nat.AtLeastTwo.prop
def one_lt : 1 < n := Nat.AtLeastTwo.prop
def ne_zero : n ≠ 0 := by have := two_le n; omega
def ne_one : n ≠ 1 := by have := two_le n; omega

def ofNat_eq_natCast [NatCast α]: OfNat.ofNat (α := α) n = ((n: Nat): α) := rfl
