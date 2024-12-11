import Math.Ops.Abs

instance : AbsoluteValue Int Nat where
  abs := Int.natAbs
