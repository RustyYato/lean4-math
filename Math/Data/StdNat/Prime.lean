namespace Nat

-- a number is atomic if it is irreducible or a unit
-- for Nat this means 1 or Prime
def IsAtomic (n: Nat): Prop := ∀m, m ∣ n -> m = 1 ∨ m = n

end Nat
