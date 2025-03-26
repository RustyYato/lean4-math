import Math.Algebra.AddMonoidWithOne.Defs
import Math.Algebra.Monoid.Hom

def resp_natCast
  [FunLike F α β]
  [AddMonoidWithOneOps α] [AddMonoidWithOneOps β]
  [IsZeroHom F α β] [IsOneHom F α β] [IsAddHom F α β]
  [IsAddMonoidWithOne α] [IsAddMonoidWithOne β]
  (f: F) (n: Nat) : f n = n := by
  induction n with
  | zero => rw [natCast_zero, natCast_zero, resp_zero]
  | succ n ih => rw [natCast_succ, natCast_succ, resp_add, ih, resp_one]

def resp_ofNat
  [FunLike F α β]
  [AddMonoidWithOneOps α] [AddMonoidWithOneOps β]
  [IsZeroHom F α β] [IsOneHom F α β] [IsAddHom F α β]
  [IsAddMonoidWithOne α] [IsAddMonoidWithOne β]
  (f: F) (n: Nat) : f (OfNat.ofNat (n + 2)) = OfNat.ofNat (n + 2) := by
  rw [ofNat_eq_natCast, resp_natCast]
  symm; apply ofNat_eq_natCast

def natCast_AddGroupHom
  [FunLike F α β] [AddMonoidWithOneOps α] [IsAddMonoidWithOne α] : ℕ →+ α where
  toFun n := n
  resp_zero' := natCast_zero
  resp_add' := by
    dsimp
    intro x y
    rw [natCast_add]
