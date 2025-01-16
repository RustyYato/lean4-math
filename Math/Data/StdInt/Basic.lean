namespace Int

def cases {motive: Int -> Sort _}
  (zero: motive 0) (pos: ∀n: Nat, motive ↑(n + 1)) (neg: ∀n: Nat, motive -[n+1]) : ∀i, motive i
| 0 => zero
| .negSucc _ => neg _
| .ofNat (.succ _) => pos _

def induction {motive : Int → Prop} (i : Int)
  (zero : motive 0) (succ : ∀i, motive i → motive (i + 1)) (pred : ∀i, motive i → motive (i - 1)) : motive i := by
induction i with
| ofNat i =>
  induction i with
  | zero => exact zero
  | succ i ih => exact succ _ ih
| negSucc i =>
  induction i with
  | zero =>
    suffices motive (0 - 1) from this
    apply pred
    assumption
  | succ n ih =>
    suffices motive (-[n+1] - 1) from this
    apply pred
    assumption

def natAbs_npow (a: Int) (n: Nat) : (a ^ n).natAbs = a.natAbs ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Int.pow_succ, Nat.pow_succ, Int.natAbs_mul, ih]

end Int
