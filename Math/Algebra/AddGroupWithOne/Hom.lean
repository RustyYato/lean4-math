import Math.Algebra.AddGroupWithOne.Defs
import Math.Algebra.AddMonoidWithOne.Hom
import Math.Algebra.Group.Hom
import Math.Data.Int.Basic

def resp_intCast
  [FunLike F α β]
  [AddGroupWithOneOps α] [AddGroupWithOneOps β]
  [IsZeroHom F α β] [IsOneHom F α β] [IsAddHom F α β]
  [IsAddGroupWithOne α] [IsAddGroupWithOne β]
  (f: F) (n: Int) : f n = n := by
  induction n with
  | ofNat n => rw [intCast_ofNat, intCast_ofNat, resp_natCast]
  | negSucc n => rw [intCast_negSucc, intCast_negSucc, resp_neg, resp_natCast]

def intCast_AddGroupHom
  [FunLike F α β] [AddGroupWithOneOps α] [IsAddGroupWithOne α] : ℤ →+ α where
  toFun n := n
  resp_zero := intCast_zero
  resp_add := by
    dsimp
    intro x y
    rw [intCast_add]
